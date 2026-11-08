#ifndef NOMINMAX
#define NOMINMAX
#endif
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif

#include "ImportMimicPass.h"

#include "DLLHelper/DLLGrabberUtility.h"
#include "DLLHelper/OfficialDLLDownloader.h"
#include "DLLHelper/DLLExportGrabber.h"

#ifdef min
#undef min
#endif
#ifdef max
#undef max
#endif

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/StringSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <filesystem>
#include <map>
#include <random>
#include <string>
#include <vector>

#ifdef _WIN32
#include <windows.h>
#endif

using namespace llvm;

llvm::cl::opt<bool> MimicEnable("obfimpmimic", llvm::cl::init(true), llvm::cl::desc("Master Toggle"));

static constexpr const char* ExtraDllsDefault = "user32.dll,winmm.dll,pdh.dll,wtsapi32.dll,crypt32.dll,shlwapi.dll,ole32.dll,oleaut32.dll,iphlpapi.dll,netapi32.dll,comctl32.dll,comdlg32.dll,shell32.dll,version.dll,psapi.dll,setupapi.dll";

static constexpr const char* SeedHostPool[] = {
    "ntdll.dll", "kernelbase.dll", "win32u.dll", "gdi32full.dll",
    "combase.dll", "sechost.dll", "shcore.dll", "bcrypt.dll", "ucrtbase.dll",
    "kernel32.dll", "user32.dll", "gdi32.dll", "advapi32.dll",
    "shell32.dll", "shlwapi.dll", "ole32.dll", "oleaut32.dll",
    "ws2_32.dll", "winhttp.dll", "wininet.dll", "msvcrt.dll",
    "crypt32.dll", "psapi.dll", "version.dll", "setupapi.dll",
    "comctl32.dll", "comdlg32.dll", "wintrust.dll", "dbghelp.dll",
    "dxgi.dll", "d3d11.dll", "d3d12.dll",
};
static constexpr unsigned SeedHostPoolSize = sizeof(SeedHostPool) / sizeof(SeedHostPool[0]);
static constexpr int MaxForwarderHops = 16;

struct HostState
{
    std::string DllLower;
    bool Sourced = false;
    std::wstring CanonicalPath;
    DLLExportGrabber::ExportTable Exports;
};

struct SiteRecord
{
    CallBase* Call = nullptr;
    Function* Caller = nullptr;
    Function* Callee = nullptr;
    unsigned ArgCount = 0;
};

struct CoverRecord
{
    std::string Name;
    std::string Dll;
    uint64_t HashedName = 0;
    bool Loaded = false;
};

struct StashSlotInfo
{
    bool IsString = false;
    unsigned ByteLen = 0;
    std::vector<uint8_t> PlaintextBytes;
};

struct MimicHelpers
{
    Function* FnvUtf16Lower = nullptr;
    Function* FnvAscii = nullptr;
    Function* FindModule = nullptr;
    Function* FindExport = nullptr;
    Function* Patch = nullptr;
    Function* PatchIat = nullptr;
};

struct MimicContext
{
    GlobalVariable* TlsPool = nullptr;
    GlobalVariable* EntropyGV = nullptr;
    MimicHelpers Helpers;
    std::mt19937_64 Rng;
    unsigned NextSiteId = 0;
};

static bool HasAnnotationTag(Function& f, const char* tag)
{
    Module* m = f.getParent();
    GlobalVariable* ga = m->getGlobalVariable("llvm.global.annotations");
    if (!ga) return false;
    ConstantArray* ca = dyn_cast<ConstantArray>(ga->getOperand(0));
    if (!ca) return false;
    for (unsigned i = 0; i < ca->getNumOperands(); ++i)
    {
        ConstantStruct* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!cs) continue;
        if (cs->getOperand(0)->stripPointerCasts() != &f) continue;
        auto* strgv = dyn_cast<GlobalVariable>(cs->getOperand(1)->stripPointerCasts());
        if (!strgv || !strgv->hasInitializer()) continue;
        auto* cds = dyn_cast<ConstantDataSequential>(strgv->getInitializer());
        if (!cds || !cds->isString()) continue;
        if (strcmp(cds->getAsString().str().c_str(), tag) == 0) return true;
    }
    return false;
}

static bool HasImpMimicAnnotation(Function& f)
{
    return HasAnnotationTag(f, "impmimic");
}

static bool HasNoImpMimicAnnotation(Function& f)
{
    return HasAnnotationTag(f, "noimpmimic");
}

static bool HasNoObfuscateAnnotation(Function& f)
{
    return HasAnnotationTag(f, "noobfus");
}

static std::string ToLowerAscii(std::string s)
{
    for (char& c : s) if (c >= 'A' && c <= 'Z') c = char(c - 'A' + 'a');
    return s;
}

static bool IsApiSet(const std::string& n)
{
    return n.rfind("api-ms-", 0) == 0 || n.rfind("ext-ms-", 0) == 0;
}

static std::string UnmangleCName(StringRef n)
{
    std::string s = n.str();
    if (!s.empty() && s[0] == '_') s.erase(0, 1);
    const size_t at = s.find('@');
    if (at != std::string::npos) s.resize(at);
    return s;
}

static constexpr uint64_t Fnv1a64(const char* s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    while (*s)
    {
        h ^= (uint8_t)(*s);
        h *= 0x100000001b3ULL;
        ++s;
    }
    return h;
}

static uint64_t Fnv1a64Range(StringRef s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    for (char c : s)
    {
        h ^= (uint8_t)c;
        h *= 0x100000001b3ULL;
    }
    return h;
}

static uint64_t Fnv1aAsciiLower(const std::string& s)
{
    uint64_t h = 0xcbf29ce484222325ULL;
    for (char c : s)
    {
        if (c >= 'A' && c <= 'Z') c = (char)(c - 'A' + 'a');
        h ^= (uint8_t)c;
        h *= 0x100000001b3ULL;
    }
    return h;
}

static bool IsImportDecl(const Function* f)
{
    if (!f) return false;
    if (!f->isDeclaration()) return false;
    if (f->isIntrinsic()) return false;
    return f->hasDLLImportStorageClass();
}

static bool SourceHost(const std::string& hostlower, HostState& out)
{
    out.DllLower = hostlower;
    out.Sourced = false;
    if (IsApiSet(hostlower)) return false;

    std::filesystem::path syspath("C:\\Windows\\System32");
    syspath /= hostlower;

    DLLGrabberUtility::DllIdentity id;
    std::wstring err;
    if (!DLLGrabberUtility::Instance().GrabIdentity(syspath.wstring(), id, err)) return false;

    OfficialDllDownloader::DownloadResult dr;
    if (OfficialDllDownloader::Instance().TryGetCachedDll(id.DllName, id.TimeDateStamp, id.SizeOfImage, dr) && dr.Success)
    {
        out.CanonicalPath = dr.OutputPath;
    }
    else if (OfficialDllDownloader::Instance().DownloadDll(id.DllName, id.TimeDateStamp, id.SizeOfImage, dr) && dr.Success)
    {
        out.CanonicalPath = dr.OutputPath;
    }
    else
    {
        return false;
    }

    if (!DLLExportGrabber::Instance().GrabExports(out.CanonicalPath, out.Exports, err)) return false;
    out.Sourced = true;
    return true;
}

static bool ResolveImport(const std::string& firsthost, const std::string& firstname, std::map<std::string, HostState>& hosts, std::string& outhost, uint32_t& outrva)
{
    std::string host = firsthost;
    std::string name = firstname;

    for (int hop = 0; hop <= MaxForwarderHops; ++hop)
    {
        if (IsApiSet(host)) return false;
        auto it = hosts.find(host);
        if (it == hosts.end())
        {
            HostState hs;
            SourceHost(host, hs);
            auto ins = hosts.emplace(host, std::move(hs));
            it = ins.first;
        }
        if (!it->second.Sourced) return false;
        const DLLExportGrabber::ExportTable& t = it->second.Exports;
        auto ni = t.NameToIndex.find(name);
        if (ni == t.NameToIndex.end()) return false;
        const DLLExportGrabber::ExportEntry& e = t.Entries[ni->second];
        if (!e.Forwarded)
        {
            outhost = host;
            outrva = e.Rva;
            return true;
        }
        if (e.ForwardApiset) return false;
        if (e.ForwardByOrdinal) return false;
        if (e.ForwardDll.empty() || e.ForwardName.empty()) return false;
        host = e.ForwardDll;
        name = e.ForwardName;
    }
    return false;
}

static std::vector<std::string> DiscoverImportedDlls(Module& m)
{
    std::vector<std::string> out;
#ifdef _WIN32
    std::map<std::string, HostState> hosts;
    DenseSet<uint64_t> seen;

    for (Function& f : m)
    {
        if (!IsImportDecl(&f)) continue;
        const std::string cname = UnmangleCName(f.getName());
        for (unsigned s = 0; s < SeedHostPoolSize; ++s)
        {
            const std::string hostlower = SeedHostPool[s];
            auto it = hosts.find(hostlower);
            if (it == hosts.end())
            {
                HostState hs;
                SourceHost(hostlower, hs);
                it = hosts.emplace(hostlower, std::move(hs)).first;
            }
            if (!it->second.Sourced) continue;
            if (!it->second.Exports.NameToIndex.count(cname)) continue;
            std::string termhost;
            uint32_t termrva = 0;
            if (ResolveImport(hostlower, cname, hosts, termhost, termrva))
            {
                if (seen.insert(Fnv1a64(termhost.c_str())).second) out.push_back(termhost);
                break;
            }
        }
    }
#else
    (void)m;
#endif
    return out;
}

static std::vector<std::string> ParseDllList(StringRef s)
{
    std::vector<std::string> out;
    std::string cur;
    auto flush = [&]()
    {
        size_t a = 0, b = cur.size();
        while (a < b && (cur[a] == ' ' || cur[a] == '\t')) ++a;
        while (b > a && (cur[b - 1] == ' ' || cur[b - 1] == '\t')) --b;
        if (b > a)
        {
            std::string t = ToLowerAscii(cur.substr(a, b - a));
            bool dup = false;
            for (const auto& x : out) if (x == t) { dup = true; break; }
            if (!dup) out.push_back(std::move(t));
        }
        cur.clear();
    };
    for (char c : s)
    {
        if (c == ',' || c == ';') flush();
        else cur += c;
    }
    flush();
    return out;
}

static bool IsSafeCoverName(StringRef n)
{
    static const StringSet<> safe = {
        "LoadLibraryA", "LoadLibraryW", "LoadLibraryExA", "LoadLibraryExW",
        "FreeLibrary", "GetModuleHandleA", "GetModuleHandleW",
        "GetModuleHandleExA", "GetModuleHandleExW",
        "GetProcAddress", "GetTickCount", "GetTickCount64", "Sleep",
        "SleepEx", "GetCurrentProcess", "GetCurrentThread",
        "GetCurrentProcessId", "GetCurrentThreadId", "CloseHandle",
        "GetLastError", "SetLastError", "GetSystemTime", "GetLocalTime",
        "GetSystemDirectoryA", "GetSystemDirectoryW",
        "GetWindowsDirectoryA", "GetWindowsDirectoryW",
        "GetTempPathA", "GetTempPathW",
        "GetCommandLineA", "GetCommandLineW",
        "CreateFileA", "CreateFileW", "ReadFile", "WriteFile",
        "DeleteFileA", "DeleteFileW", "MoveFileA", "MoveFileW",
        "CopyFileA", "CopyFileW",
        "GetFileAttributesA", "GetFileAttributesW",
        "SetFileAttributesA", "SetFileAttributesW",
        "FindFirstFileA", "FindFirstFileW",
        "FindNextFileA", "FindNextFileW", "FindClose",
        "CreateDirectoryA", "CreateDirectoryW",
        "RemoveDirectoryA", "RemoveDirectoryW",
        "GetCurrentDirectoryA", "GetCurrentDirectoryW",
        "SetCurrentDirectoryA", "SetCurrentDirectoryW",
        "GetFileSize", "GetFileSizeEx",
        "SetFilePointer", "SetFilePointerEx",
        "GetFileTime", "SetFileTime",
        "HeapAlloc", "HeapFree", "HeapReAlloc", "HeapCreate", "HeapDestroy",
        "VirtualAlloc", "VirtualFree", "VirtualProtect", "VirtualQuery",
        "GetVersion", "GetVersionExA", "GetVersionExW",
        "GetModuleFileNameA", "GetModuleFileNameW",
        "GetVolumeInformationA", "GetVolumeInformationW",
        "GetDiskFreeSpaceA", "GetDiskFreeSpaceW",
        "GetVolumePathNameA", "GetVolumePathNameW",
        "GetDriveTypeA", "GetDriveTypeW",
        "GetEnvironmentVariableA", "GetEnvironmentVariableW",
        "SetEnvironmentVariableA", "SetEnvironmentVariableW",
        "ExpandEnvironmentStringsA", "ExpandEnvironmentStringsW",
        "FormatMessageA", "FormatMessageW",
        "lstrlenA", "lstrlenW", "lstrcpyA", "lstrcpyW",
        "lstrcatA", "lstrcatW", "lstrcmpA", "lstrcmpW",
        "lstrcmpiA", "lstrcmpiW",
        "QueryPerformanceCounter", "QueryPerformanceFrequency",
        "MessageBoxA", "MessageBoxW",
        "FindWindowA", "FindWindowW",
        "FindWindowExA", "FindWindowExW",
        "GetWindowRect", "GetClientRect",
        "SetCursor", "ShowWindow", "UpdateWindow",
        "GetWindowTextA", "GetWindowTextW",
        "SetWindowTextA", "SetWindowTextW",
        "SendMessageA", "SendMessageW",
        "PostMessageA", "PostMessageW",
        "GetWindowThreadProcessId",
        "IsWindow", "IsWindowVisible",
        "GetDesktopWindow", "GetForegroundWindow",
        "SetForegroundWindow", "GetActiveWindow",
        "LoadCursorA", "LoadCursorW",
        "LoadIconA", "LoadIconW",
        "GetSystemMetrics",
        "RegOpenKeyA", "RegOpenKeyW",
        "RegOpenKeyExA", "RegOpenKeyExW",
        "RegCloseKey",
        "RegQueryValueA", "RegQueryValueW",
        "RegQueryValueExA", "RegQueryValueExW",
        "RegSetValueA", "RegSetValueW",
        "RegSetValueExA", "RegSetValueExW",
        "RegCreateKeyA", "RegCreateKeyW",
        "RegCreateKeyExA", "RegCreateKeyExW",
        "RegDeleteKeyA", "RegDeleteKeyW",
        "RegDeleteValueA", "RegDeleteValueW",
        "RegEnumKeyA", "RegEnumKeyW",
        "RegEnumValueA", "RegEnumValueW",
        "OpenProcessToken", "OpenThreadToken",
        "GetTokenInformation",
        "ShellExecuteA", "ShellExecuteW",
        "SHGetFolderPathA", "SHGetFolderPathW",
        "SHGetSpecialFolderPathA", "SHGetSpecialFolderPathW",
        "CoInitialize", "CoInitializeEx", "CoUninitialize",
        "CoCreateInstance", "CoTaskMemAlloc", "CoTaskMemFree",
        "CoCreateGuid", "StringFromGUID2",
        "SysAllocString", "SysFreeString", "SysStringLen",
        "VariantInit", "VariantClear", "VariantCopy",
        "CreateCompatibleDC", "DeleteDC",
        "CreateCompatibleBitmap", "DeleteObject",
        "SelectObject", "GetStockObject",
        "BitBlt", "StretchBlt",
        "PathFileExistsA", "PathFileExistsW",
        "PathAppendA", "PathAppendW",
        "PathCombineA", "PathCombineW",
        "PathRemoveFileSpecA", "PathRemoveFileSpecW",
        "PathFindExtensionA", "PathFindExtensionW",
        "StrCmpIA", "StrCmpIW",
    };
    return safe.contains(n);
}

static bool IsCoverCrtExcluded(StringRef n)
{
    // prefix buckets subsume whole families and MUST run before the exact hash switch; otherwise a case label would need every Rtl*/Nt*/Zw*/Interlocked* name spelled out, and new OS releases silently miss any additions
    if (n.starts_with("Rtl")) return true;
    if (n.starts_with("Nt")) return true;
    if (n.starts_with("Zw")) return true;
    if (n.starts_with("Interlocked")) return true;
    if (n.starts_with("EnterCriticalSection")) return true;
    if (n.starts_with("LeaveCriticalSection")) return true;
    if (n.starts_with("InitializeCriticalSection")) return true;
    if (n.starts_with("DeleteCriticalSection")) return true;
    if (n.starts_with("TryEnterCriticalSection")) return true;
    if (n.starts_with("AcquireSRWLock")) return true;
    if (n.starts_with("ReleaseSRWLock")) return true;
    if (n.starts_with("InitializeSRWLock")) return true;
    if (n.starts_with("TryAcquireSRWLock")) return true;
    if (n.starts_with("WakeConditionVariable")) return true;
    if (n.starts_with("SleepConditionVariable")) return true;
    if (n.starts_with("InitializeConditionVariable")) return true;

    switch (Fnv1a64Range(n))
    {
        case Fnv1a64("GetLastError"):
        case Fnv1a64("SetLastError"):
        case Fnv1a64("GetCurrentThreadId"):
        case Fnv1a64("GetCurrentProcessId"):
        case Fnv1a64("GetCurrentProcess"):
        case Fnv1a64("GetCurrentThread"):
        case Fnv1a64("GetTickCount"):
        case Fnv1a64("GetTickCount64"):
        case Fnv1a64("QueryPerformanceCounter"):
        case Fnv1a64("QueryPerformanceFrequency"):
        case Fnv1a64("GetSystemTimeAsFileTime"):
        case Fnv1a64("GetSystemTime"):
        case Fnv1a64("GetLocalTime"):
        case Fnv1a64("GetModuleHandleW"):
        case Fnv1a64("GetModuleHandleA"):
        case Fnv1a64("GetModuleHandleExW"):
        case Fnv1a64("GetModuleHandleExA"):
        case Fnv1a64("GetModuleFileNameW"):
        case Fnv1a64("GetModuleFileNameA"):
        case Fnv1a64("GetProcAddress"):
        case Fnv1a64("LoadLibraryW"):
        case Fnv1a64("LoadLibraryA"):
        case Fnv1a64("LoadLibraryExW"):
        case Fnv1a64("LoadLibraryExA"):
        case Fnv1a64("FreeLibrary"):
        case Fnv1a64("FreeLibraryAndExitThread"):
        case Fnv1a64("DisableThreadLibraryCalls"):
        case Fnv1a64("VirtualAlloc"):
        case Fnv1a64("VirtualAllocEx"):
        case Fnv1a64("VirtualFree"):
        case Fnv1a64("VirtualProtect"):
        case Fnv1a64("VirtualProtectEx"):
        case Fnv1a64("VirtualQuery"):
        case Fnv1a64("VirtualQueryEx"):
        case Fnv1a64("HeapCreate"):
        case Fnv1a64("HeapDestroy"):
        case Fnv1a64("HeapAlloc"):
        case Fnv1a64("HeapReAlloc"):
        case Fnv1a64("HeapFree"):
        case Fnv1a64("HeapSize"):
        case Fnv1a64("HeapValidate"):
        case Fnv1a64("HeapCompact"):
        case Fnv1a64("HeapLock"):
        case Fnv1a64("HeapUnlock"):
        case Fnv1a64("HeapSetInformation"):
        case Fnv1a64("HeapQueryInformation"):
        case Fnv1a64("GetProcessHeap"):
        case Fnv1a64("GetProcessHeaps"):
        case Fnv1a64("TlsAlloc"):
        case Fnv1a64("TlsGetValue"):
        case Fnv1a64("TlsSetValue"):
        case Fnv1a64("TlsFree"):
        case Fnv1a64("FlsAlloc"):
        case Fnv1a64("FlsGetValue"):
        case Fnv1a64("FlsSetValue"):
        case Fnv1a64("FlsFree"):
        case Fnv1a64("EncodePointer"):
        case Fnv1a64("DecodePointer"):
        case Fnv1a64("IsProcessorFeaturePresent"):
        case Fnv1a64("IsDebuggerPresent"):
        case Fnv1a64("CheckRemoteDebuggerPresent"):
        case Fnv1a64("InitializeSListHead"):
        case Fnv1a64("RaiseException"):
        case Fnv1a64("RaiseFailFastException"):
        case Fnv1a64("UnhandledExceptionFilter"):
        case Fnv1a64("SetUnhandledExceptionFilter"):
        case Fnv1a64("AddVectoredExceptionHandler"):
        case Fnv1a64("RemoveVectoredExceptionHandler"):
        case Fnv1a64("AddVectoredContinueHandler"):
        case Fnv1a64("RemoveVectoredContinueHandler"):
        case Fnv1a64("__C_specific_handler"):
        case Fnv1a64("__CxxFrameHandler3"):
        case Fnv1a64("__CxxFrameHandler4"):
        case Fnv1a64("TerminateProcess"):
        case Fnv1a64("ExitProcess"):
        case Fnv1a64("ExitThread"):
        case Fnv1a64("GetStartupInfoW"):
        case Fnv1a64("GetStartupInfoA"):
        case Fnv1a64("GetCommandLineW"):
        case Fnv1a64("GetCommandLineA"):
        case Fnv1a64("GetEnvironmentStringsW"):
        case Fnv1a64("FreeEnvironmentStringsW"):
        case Fnv1a64("GetEnvironmentVariableW"):
        case Fnv1a64("SetEnvironmentVariableW"):
        case Fnv1a64("GetStdHandle"):
        case Fnv1a64("SetStdHandle"):
        case Fnv1a64("GetFileType"):
            return true;
    }
    return false;
}

static bool IsCoverCompilerHelper(StringRef n)
{
    if (n.starts_with("__chkstk")) return true;
    if (n.starts_with("__security_")) return true;
    if (n.starts_with("__GSHandler")) return true;
    if (n.starts_with("_RTC_")) return true;
    if (n.starts_with("__scrt_")) return true;
    if (n.starts_with("__acrt_")) return true;
    if (n.starts_with("__crt_")) return true;
    if (n.starts_with("_Init_thread")) return true;
    if (n.starts_with("llvm.")) return true;

    switch (Fnv1a64Range(n))
    {
        case Fnv1a64("_purecall"):
        case Fnv1a64("__purecall"):
        case Fnv1a64("__std_terminate"):
        case Fnv1a64("__std_exception_copy"):
        case Fnv1a64("__std_exception_destroy"):
        case Fnv1a64("__CxxThrowException"):
        case Fnv1a64("__RTDynamicCast"):
        case Fnv1a64("__RTtypeid"):
        case Fnv1a64("__RTCastToVoid"):
            return true;
    }
    return false;
}

static bool IsCrtSpecialFunctionName(StringRef n)
{
    if (n.starts_with("_tls_callback")) return true;

    switch (Fnv1a64Range(n))
    {
        case Fnv1a64("DllMain"):
        case Fnv1a64("_DllMainCRTStartup"):
        case Fnv1a64("DllMainCRTStartup"):
        case Fnv1a64("mainCRTStartup"):
        case Fnv1a64("wmainCRTStartup"):
        case Fnv1a64("WinMainCRTStartup"):
        case Fnv1a64("wWinMainCRTStartup"):
        case Fnv1a64("_CRT_INIT"):
        case Fnv1a64("__scrt_common_main"):
        case Fnv1a64("__scrt_common_main_seh"):
        case Fnv1a64("__scrt_dllmain_before_initialize_c"):
        case Fnv1a64("__scrt_dllmain_after_initialize_c"):
            return true;
    }
    return false;
}

static bool IsEligibilityCompilerHelper(StringRef n)
{
    if (n.starts_with("__GSHandlerCheck")) return true;
    if (n.starts_with("_RTC_")) return true;
    if (n.starts_with("__scrt_")) return true;
    if (n.starts_with("__acrt_")) return true;
    if (n.starts_with("__crt_")) return true;

    switch (Fnv1a64Range(n))
    {
        case Fnv1a64("_chkstk"):
        case Fnv1a64("__chkstk"):
        case Fnv1a64("__chkstk_ms"):
        case Fnv1a64("__security_check_cookie"):
        case Fnv1a64("__security_init_cookie"):
        case Fnv1a64("__CxxFrameHandler3"):
        case Fnv1a64("__CxxFrameHandler4"):
        case Fnv1a64("__C_specific_handler"):
        case Fnv1a64("__CxxThrowException"):
        case Fnv1a64("__std_terminate"):
        case Fnv1a64("__std_exception_copy"):
        case Fnv1a64("__std_exception_destroy"):
        case Fnv1a64("__RTDynamicCast"):
        case Fnv1a64("__RTtypeid"):
        case Fnv1a64("__RTCastToVoid"):
        case Fnv1a64("_purecall"):
        case Fnv1a64("__purecall"):
        case Fnv1a64("__report_rangecheckfailure"):
        case Fnv1a64("__report_securityfailure"):
        case Fnv1a64("_Init_thread_header"):
        case Fnv1a64("_Init_thread_footer"):
        case Fnv1a64("_Init_thread_abort"):
        case Fnv1a64("_Init_thread_epoch"):
        case Fnv1a64("__msvc_align"):
            return true;
    }
    return false;
}

static bool IsOurEmittedHelper(StringRef n)
{
    return n.starts_with("ImpMimic");
}

static bool IsVtableGlobal(StringRef n)
{
    if (n.starts_with("??_7")) return true;
    if (n.starts_with("??_R4")) return true;
    if (n.starts_with("_ZTV")) return true;
    if (n.starts_with("_ZTC")) return true;
    if (n.starts_with("_ZTT")) return true;
    return false;
}

static Function* ResolveCalleeFn(CallBase* cb)
{
    if (Function* f = cb->getCalledFunction()) return f;
    Value* v = cb->getCalledOperand();
    if (!v) return nullptr;
    v = v->stripPointerCasts();
    for (unsigned i = 0; i < 8; ++i)
    {
        auto* ga = dyn_cast<GlobalAlias>(v);
        if (!ga) break;
        Constant* aliasee = ga->getAliasee();
        if (!aliasee) break;
        v = aliasee->stripPointerCasts();
    }
    return dyn_cast<Function>(v);
}

static bool ClassifySite(CallBase* cb, Function*& outcallee)
{
    outcallee = nullptr;
    if (cb->isInlineAsm()) return false;
    if (isa<CallBrInst>(cb)) return false;
    if (isa<InvokeInst>(cb)) return false;
    if (auto* ci = dyn_cast<CallInst>(cb))
        if (ci->isMustTailCall()) return false;
    Function* callee = ResolveCalleeFn(cb);
    if (!callee) return false;
    if (callee->isIntrinsic()) return false;
    if (!IsImportDecl(callee)) return false;
    FunctionType* ft = callee->getFunctionType();
    if (ft->isVarArg()) return false;
    if (ft->getNumParams() == 0) return false;
    outcallee = callee;
    return true;
}

static unsigned ChooseStashCount(unsigned argcount)
{
    return std::min<unsigned>(argcount, 4);
}

static GlobalVariable* GetStringLiteralGV(Value* v, unsigned& outbytelen, bool& outiswide)
{
    for (unsigned guard = 0; guard < 8; ++guard)
    {
        v = v->stripPointerCasts();
        if (auto* ce = dyn_cast<ConstantExpr>(v))
        {
            if (ce->getOpcode() == Instruction::GetElementPtr)
            {
                v = ce->getOperand(0);
                continue;
            }
        }
        if (auto* gep = dyn_cast<GetElementPtrInst>(v))
        {
            v = gep->getPointerOperand();
            continue;
        }
        break;
    }
    auto* gv = dyn_cast<GlobalVariable>(v);
    if (!gv) return nullptr;
    if (!gv->isConstant()) return nullptr;
    if (!gv->hasInitializer()) return nullptr;
    auto* arrt = dyn_cast<ArrayType>(gv->getValueType());
    if (!arrt) return nullptr;
    Type* elemt = arrt->getElementType();
    if (!elemt->isIntegerTy(8) && !elemt->isIntegerTy(16)) return nullptr;
    auto* cds = dyn_cast<ConstantDataSequential>(gv->getInitializer());
    if (!cds) return nullptr;
    outiswide = elemt->isIntegerTy(16);
    outbytelen = (unsigned)(arrt->getNumElements() * (outiswide ? 2 : 1));
    if (outbytelen == 0 || outbytelen > 4096) return nullptr;
    return gv;
}

static std::vector<uint64_t> GenArgMasks(std::mt19937_64& rng, unsigned n)
{
    std::vector<uint64_t> out(n);
    for (unsigned i = 0; i < n; ++i)
    {
        uint64_t m = rng();
        while (m == 0 || m == ~0ULL) m = rng();
        out[i] = m;
    }
    return out;
}

static void CollectGlobalCtorDtorFuncs(Module& m, DenseSet<Function*>& out)
{
    const StringRef tables[] = {"llvm.global_ctors", "llvm.global_dtors"};
    for (StringRef tn : tables)
    {
        GlobalVariable* gv = m.getNamedGlobal(tn);
        if (!gv || !gv->hasInitializer()) continue;
        auto* ca = dyn_cast<ConstantArray>(gv->getInitializer());
        if (!ca) continue;
        for (unsigned i = 0; i < ca->getNumOperands(); ++i)
        {
            auto* cs = dyn_cast<ConstantStruct>(ca->getOperand(i));
            if (!cs || cs->getNumOperands() < 2) continue;
            Value* v = cs->getOperand(1)->stripPointerCasts();
            if (auto* f = dyn_cast<Function>(v)) out.insert(f);
        }
    }
}

static void CollectFunctionsFromConstant(Constant* c, DenseSet<Function*>& out, DenseSet<Constant*>& visited)
{
    if (!c) return;
    if (!visited.insert(c).second) return;
    if (auto* f = dyn_cast<Function>(c))
    {
        out.insert(f);
        return;
    }
    for (unsigned i = 0, n = c->getNumOperands(); i < n; ++i)
    {
        if (auto* sub = dyn_cast<Constant>(c->getOperand(i))) CollectFunctionsFromConstant(sub, out, visited);
    }
}

static void CollectVtableFuncs(Module& m, DenseSet<Function*>& out)
{
    DenseSet<Constant*> visited;
    for (GlobalVariable& gv : m.globals())
    {
        if (!gv.hasInitializer()) continue;
        if (!IsVtableGlobal(gv.getName())) continue;
        CollectFunctionsFromConstant(gv.getInitializer(), out, visited);
    }
}

static bool UserLeadsOnlyToMetadataGlobals(User* u, DenseSet<User*>& visited)
{
    if (!visited.insert(u).second) return true;
    if (auto* gv = dyn_cast<GlobalVariable>(u))
    {
        StringRef n = gv->getName();
        return n == "llvm.global.annotations" || n == "llvm.used" || n == "llvm.compiler.used" || n == "llvm.metadata";
    }
    if (isa<Instruction>(u)) return false;
    if (u->user_empty()) return false;
    for (User* uu : u->users())
        if (!UserLeadsOnlyToMetadataGlobals(uu, visited)) return false;
    return true;
}

static bool DetectAddressTaken(Function& f)
{
    for (User* u : f.users())
    {
        if (auto* cb = dyn_cast<CallBase>(u))
        {
            if (cb->getCalledOperand() != &f) return true;
            continue;
        }
        DenseSet<User*> visited;
        if (!UserLeadsOnlyToMetadataGlobals(u, visited)) return true;
    }
    return false;
}

static void CollectCrtReachable(Module& m, const DenseSet<Function*>& ctordtorset, DenseSet<Function*>& outreachable)
{
    SmallVector<Function*, 32> work;
    for (Function& f : m)
    {
        if (f.isDeclaration()) continue;
        StringRef n = f.getName();
        if (IsCrtSpecialFunctionName(n) || IsEligibilityCompilerHelper(n) || ctordtorset.contains(&f))
        {
            if (outreachable.insert(&f).second) work.push_back(&f);
        }
    }
    while (!work.empty())
    {
        Function* cur = work.pop_back_val();
        for (BasicBlock& bb : *cur)
        {
            for (Instruction& i : bb)
            {
                auto* cb = dyn_cast<CallBase>(&i);
                if (!cb) continue;
                // indirect calls can't be statically tracked and conservatively do not propagate pre crt taint
                Function* callee = cb->getCalledFunction();
                if (!callee || callee->isDeclaration()) continue;
                if (outreachable.insert(callee).second) work.push_back(callee);
            }
        }
    }
}

static void BuildEligibleSet(Module& m, DenseSet<Function*>& outeligible)
{
    DenseSet<Function*> ctordtorset;
    DenseSet<Function*> vtableset;
    CollectGlobalCtorDtorFuncs(m, ctordtorset);
    CollectVtableFuncs(m, vtableset);

    DenseSet<Function*> crtreachable;
    CollectCrtReachable(m, ctordtorset, crtreachable);

    for (Function& f : m)
    {
        if (f.isDeclaration() || f.isIntrinsic()) continue;
        StringRef name = f.getName();
        if (IsOurEmittedHelper(name)) continue;
        if (f.hasFnAttribute(Attribute::Naked)) continue;
        if (IsCrtSpecialFunctionName(name)) continue;
        if (IsEligibilityCompilerHelper(name)) continue;
        if (ctordtorset.contains(&f)) continue;
        if (vtableset.contains(&f)) continue;
        if (HasNoObfuscateAnnotation(f)) continue;
        if (f.hasPersonalityFn()) continue;
        if (f.isVarArg()) continue;
        if (DetectAddressTaken(f)) continue;
        if (crtreachable.contains(&f)) continue;

        bool bad = false;
        for (BasicBlock& bb : f)
        {
            for (Instruction& i : bb)
            {
                if (isa<FuncletPadInst>(&i)) { bad = true; break; }
                if (isa<CatchReturnInst>(&i)) { bad = true; break; }
                if (isa<CleanupReturnInst>(&i)) { bad = true; break; }
                if (isa<InvokeInst>(&i)) { bad = true; break; }
                if (auto* ci = dyn_cast<CallInst>(&i))
                    if (ci->isMustTailCall()) { bad = true; break; }
            }
            if (bad) break;
        }
        if (bad) continue;

        bool invokecaller = false;
        for (User* u : f.users())
        {
            auto* cb = dyn_cast<CallBase>(u);
            if (!cb) continue;
            if (cb->getCalledOperand() != &f) continue;
            if (isa<InvokeInst>(cb) || isa<CallBrInst>(cb))
            {
                invokecaller = true;
                break;
            }
        }
        if (invokecaller) continue;

        outeligible.insert(&f);
    }
}

static Function* WalkUpwardFromCaller(Function* p, Function* f, const DenseSet<Function*>& eligibleset, unsigned depthcap)
{
    if (!eligibleset.contains(p)) return nullptr;

    DenseSet<Function*> visited;
    visited.insert(f);
    visited.insert(p);

    Function* stopat = p;
    unsigned depth = 1;

    Function* cur = p;
    while (true)
    {
        if (depth >= depthcap) break;

        Function* singlecaller = nullptr;
        unsigned callinstcount = 0;
        bool hasinvokecaller = false;
        bool hasnoneligcaller = false;

        for (User* u : cur->users())
        {
            auto* cb = dyn_cast<CallBase>(u);
            if (!cb) continue;
            if (cb->getCalledOperand() != cur) continue;
            if (isa<InvokeInst>(cb) || isa<CallBrInst>(cb))
            {
                hasinvokecaller = true;
                continue;
            }
            auto* ci = dyn_cast<CallInst>(cb);
            if (!ci) continue;
            Function* q = ci->getFunction();
            if (!eligibleset.contains(q))
            {
                hasnoneligcaller = true;
                continue;
            }
            if (callinstcount == 0) singlecaller = q;
            else if (singlecaller != q) singlecaller = (Function*)1;
            ++callinstcount;
        }

        if (hasinvokecaller) break;
        if (callinstcount == 0 && hasnoneligcaller) break;
        if (callinstcount == 0) break;
        if (callinstcount > 1 && singlecaller == (Function*)1) break;
        if (callinstcount > 1) break;

        Function* next = singlecaller;
        if (!visited.insert(next).second) break;

        cur = next;
        stopat = cur;
        ++depth;
    }

    return stopat;
}

static Function* FindInstallPoint(Function* sitecaller, Function* sitecallee, const DenseSet<Function*>& eligibleset)
{
    return WalkUpwardFromCaller(sitecaller, sitecallee, eligibleset, 32);
}

static void AddInstallSequence(Function* fn, Function* installerfn, GlobalVariable* guardgv)
{
    LLVMContext& c = fn->getContext();
    Type* i8 = Type::getInt8Ty(c);

    BasicBlock& entry = fn->getEntryBlock();
    Instruction* firsti = &*entry.getFirstInsertionPt();

    BasicBlock* proceedbb = entry.splitBasicBlock(firsti, "ImpMimicProceed");
    entry.getTerminator()->eraseFromParent();

    BasicBlock* installbb = BasicBlock::Create(c, "ImpMimicInstall", fn, proceedbb);
    {
        IRBuilder<> b(installbb);
        b.CreateCall(FunctionType::get(Type::getVoidTy(c), {}, false), installerfn, {});
        b.CreateBr(proceedbb);
    }
    {
        IRBuilder<> b(&entry);
        Value* g = b.CreateLoad(i8, guardgv);
        Value* need = b.CreateICmpEQ(g, ConstantInt::get(i8, 0));
        b.CreateCondBr(need, installbb, proceedbb);
    }
}

static std::vector<unsigned> GenTlsPermutation(std::mt19937_64& rng, unsigned n)
{
    std::vector<unsigned> all = {1, 2, 3, 4, 5, 6, 7};
    std::shuffle(all.begin(), all.end(), rng);
    if (n > all.size()) n = all.size();
    all.resize(n);
    return all;
}

static void CreateMimicHelpers(Module& m, MimicHelpers& h)
{
    if (h.FnvAscii) return;

    LLVMContext& c = m.getContext();
    Type* i8 = Type::getInt8Ty(c);
    Type* i16 = Type::getInt16Ty(c);
    Type* i32 = Type::getInt32Ty(c);
    Type* i64 = Type::getInt64Ty(c);
    Type* voidt = Type::getVoidTy(c);
    PointerType* ptrty = PointerType::get(c, 0);
    PointerType* gsptr = PointerType::get(c, 256);

    Constant* fnvoffset = ConstantInt::get(i64, 0xcbf29ce484222325ULL);
    Constant* fnvprime = ConstantInt::get(i64, 0x100000001b3ULL);

    {
        FunctionType* ft = FunctionType::get(i64, {ptrty}, false);
        h.FnvAscii = Function::Create(ft, GlobalValue::InternalLinkage, "ImpMimicFnvAscii", m);
        h.FnvAscii->addFnAttr(Attribute::NoInline);
        h.FnvAscii->addFnAttr(Attribute::UWTable);

        BasicBlock* entry = BasicBlock::Create(c, "Entry", h.FnvAscii);
        BasicBlock* loop = BasicBlock::Create(c, "Loop", h.FnvAscii);
        BasicBlock* body = BasicBlock::Create(c, "Body", h.FnvAscii);
        BasicBlock* done = BasicBlock::Create(c, "Done", h.FnvAscii);

        Argument* strarg = h.FnvAscii->getArg(0);

        IRBuilder<> b(entry);
        b.CreateBr(loop);

        b.SetInsertPoint(loop);
        PHINode* iphi = b.CreatePHI(i64, 2, "Index");
        PHINode* hphi = b.CreatePHI(i64, 2, "Hash");
        iphi->addIncoming(ConstantInt::get(i64, 0), entry);
        hphi->addIncoming(fnvoffset, entry);
        Value* p = b.CreateGEP(i8, strarg, iphi);
        Value* ch = b.CreateLoad(i8, p);
        Value* isnull = b.CreateICmpEQ(ch, ConstantInt::get(i8, 0));
        b.CreateCondBr(isnull, done, body);

        b.SetInsertPoint(body);
        Value* c64 = b.CreateZExt(ch, i64);
        Value* hxor = b.CreateXor(hphi, c64);
        Value* hmul = b.CreateMul(hxor, fnvprime);
        Value* inxt = b.CreateAdd(iphi, ConstantInt::get(i64, 1));
        iphi->addIncoming(inxt, body);
        hphi->addIncoming(hmul, body);
        b.CreateBr(loop);

        b.SetInsertPoint(done);
        b.CreateRet(hphi);
    }

    {
        FunctionType* ft = FunctionType::get(i64, {ptrty, i64}, false);
        h.FnvUtf16Lower = Function::Create(ft, GlobalValue::InternalLinkage, "ImpMimicFnvUtf16Lower", m);
        h.FnvUtf16Lower->addFnAttr(Attribute::NoInline);
        h.FnvUtf16Lower->addFnAttr(Attribute::UWTable);

        BasicBlock* entry = BasicBlock::Create(c, "Entry", h.FnvUtf16Lower);
        BasicBlock* loop = BasicBlock::Create(c, "Loop", h.FnvUtf16Lower);
        BasicBlock* body = BasicBlock::Create(c, "Body", h.FnvUtf16Lower);
        BasicBlock* done = BasicBlock::Create(c, "Done", h.FnvUtf16Lower);

        Argument* bufarg = h.FnvUtf16Lower->getArg(0);
        Argument* nchararg = h.FnvUtf16Lower->getArg(1);

        IRBuilder<> b(entry);
        b.CreateBr(loop);

        b.SetInsertPoint(loop);
        PHINode* iphi = b.CreatePHI(i64, 2, "Index");
        PHINode* hphi = b.CreatePHI(i64, 2, "Hash");
        iphi->addIncoming(ConstantInt::get(i64, 0), entry);
        hphi->addIncoming(fnvoffset, entry);
        Value* atend = b.CreateICmpUGE(iphi, nchararg);
        b.CreateCondBr(atend, done, body);

        b.SetInsertPoint(body);
        Value* p = b.CreateGEP(i16, bufarg, iphi);
        Value* w = b.CreateLoad(i16, p);
        Value* ch = b.CreateTrunc(w, i8);
        Value* gea = b.CreateICmpUGE(ch, ConstantInt::get(i8, 'A'));
        Value* lez = b.CreateICmpULE(ch, ConstantInt::get(i8, 'Z'));
        Value* isupper = b.CreateAnd(gea, lez);
        Value* clow = b.CreateAdd(ch, ConstantInt::get(i8, 32));
        Value* cfinal = b.CreateSelect(isupper, clow, ch);
        Value* c64 = b.CreateZExt(cfinal, i64);
        Value* hxor = b.CreateXor(hphi, c64);
        Value* hmul = b.CreateMul(hxor, fnvprime);
        Value* inxt = b.CreateAdd(iphi, ConstantInt::get(i64, 1));
        iphi->addIncoming(inxt, body);
        hphi->addIncoming(hmul, body);
        b.CreateBr(loop);

        b.SetInsertPoint(done);
        b.CreateRet(hphi);
    }

    {
        FunctionType* ft = FunctionType::get(ptrty, {i64}, false);
        h.FindModule = Function::Create(ft, GlobalValue::InternalLinkage, "ImpMimicFindModule", m);
        h.FindModule->addFnAttr(Attribute::NoInline);
        h.FindModule->addFnAttr(Attribute::UWTable);

        Argument* targethash = h.FindModule->getArg(0);

        BasicBlock* entry = BasicBlock::Create(c, "Entry", h.FindModule);
        BasicBlock* loop = BasicBlock::Create(c, "Loop", h.FindModule);
        BasicBlock* check = BasicBlock::Create(c, "Check", h.FindModule);
        BasicBlock* advance = BasicBlock::Create(c, "Advance", h.FindModule);
        BasicBlock* found = BasicBlock::Create(c, "Found", h.FindModule);
        BasicBlock* notfound = BasicBlock::Create(c, "NotFound", h.FindModule);

        IRBuilder<> b(entry);
        Value* gsslot = b.CreateIntToPtr(ConstantInt::get(i64, 0x60), gsptr);
        Value* peb = b.CreateLoad(ptrty, gsslot);
        Value* ldrslot = b.CreateGEP(i8, peb, ConstantInt::get(i64, 0x18));
        Value* ldr = b.CreateLoad(ptrty, ldrslot);
        Value* head = b.CreateGEP(i8, ldr, ConstantInt::get(i64, 0x10));
        Value* firstentry = b.CreateLoad(ptrty, head);
        b.CreateBr(loop);

        b.SetInsertPoint(loop);
        PHINode* curr = b.CreatePHI(ptrty, 2, "Current");
        curr->addIncoming(firstentry, entry);
        Value* atend = b.CreateICmpEQ(curr, head);
        b.CreateCondBr(atend, notfound, check);

        b.SetInsertPoint(check);
        Value* lenptr = b.CreateGEP(i8, curr, ConstantInt::get(i64, 0x58));
        Value* lenu16 = b.CreateLoad(i16, lenptr);
        Value* len64 = b.CreateZExt(lenu16, i64);
        Value* nchar = b.CreateLShr(len64, ConstantInt::get(i64, 1));
        Value* bufptr = b.CreateGEP(i8, curr, ConstantInt::get(i64, 0x60));
        Value* buf = b.CreateLoad(ptrty, bufptr);
        Value* hash = b.CreateCall(h.FnvUtf16Lower, {buf, nchar});
        Value* match = b.CreateICmpEQ(hash, targethash);
        b.CreateCondBr(match, found, advance);

        b.SetInsertPoint(found);
        Value* dllbaseptr = b.CreateGEP(i8, curr, ConstantInt::get(i64, 0x30));
        Value* dllbase = b.CreateLoad(ptrty, dllbaseptr);
        b.CreateRet(dllbase);

        b.SetInsertPoint(advance);
        Value* nextentry = b.CreateLoad(ptrty, curr);
        curr->addIncoming(nextentry, advance);
        b.CreateBr(loop);

        b.SetInsertPoint(notfound);
        b.CreateRet(ConstantPointerNull::get(ptrty));
    }

    {
        FunctionType* ft = FunctionType::get(ptrty, {ptrty, i64}, false);
        h.FindExport = Function::Create(ft, GlobalValue::InternalLinkage, "ImpMimicFindExport", m);
        h.FindExport->addFnAttr(Attribute::NoInline);
        h.FindExport->addFnAttr(Attribute::UWTable);

        Argument* basearg = h.FindExport->getArg(0);
        Argument* targethash = h.FindExport->getArg(1);

        BasicBlock* entry = BasicBlock::Create(c, "Entry", h.FindExport);
        BasicBlock* nullbase = BasicBlock::Create(c, "NullBase", h.FindExport);
        BasicBlock* parse = BasicBlock::Create(c, "Parse", h.FindExport);
        BasicBlock* loop = BasicBlock::Create(c, "Loop", h.FindExport);
        BasicBlock* check = BasicBlock::Create(c, "Check", h.FindExport);
        BasicBlock* advance = BasicBlock::Create(c, "Advance", h.FindExport);
        BasicBlock* found = BasicBlock::Create(c, "Found", h.FindExport);
        BasicBlock* notfound = BasicBlock::Create(c, "NotFound", h.FindExport);

        IRBuilder<> b(entry);
        Value* isnull = b.CreateICmpEQ(basearg, ConstantPointerNull::get(ptrty));
        b.CreateCondBr(isnull, nullbase, parse);

        b.SetInsertPoint(nullbase);
        b.CreateRet(ConstantPointerNull::get(ptrty));

        b.SetInsertPoint(parse);
        Value* lfanewptr = b.CreateGEP(i8, basearg, ConstantInt::get(i64, 0x3C));
        Value* lfanew = b.CreateLoad(i32, lfanewptr);
        Value* lfanew64 = b.CreateZExt(lfanew, i64);
        Value* nt = b.CreateGEP(i8, basearg, lfanew64);
        Value* edvrvaptr = b.CreateGEP(i8, nt, ConstantInt::get(i64, 0x88));
        Value* edrva = b.CreateLoad(i32, edvrvaptr);
        Value* edrva64 = b.CreateZExt(edrva, i64);
        Value* ed = b.CreateGEP(i8, basearg, edrva64);
        // a forwarder's AddressOfFunctions[ord] rva points into the Export Directory itself (at the forwarder string), not real code; hooking there faults DEP
        Value* edsizeptr = b.CreateGEP(i8, nt, ConstantInt::get(i64, 0x8C));
        Value* edsize = b.CreateLoad(i32, edsizeptr);
        Value* edsize64 = b.CreateZExt(edsize, i64);
        Value* edend = b.CreateGEP(i8, ed, edsize64);
        Value* nnptr = b.CreateGEP(i8, ed, ConstantInt::get(i64, 0x18));
        Value* nn = b.CreateLoad(i32, nnptr);
        Value* nn64 = b.CreateZExt(nn, i64);
        Value* funcrvaptr = b.CreateGEP(i8, ed, ConstantInt::get(i64, 0x1C));
        Value* funcrva = b.CreateLoad(i32, funcrvaptr);
        Value* funcrva64 = b.CreateZExt(funcrva, i64);
        Value* funcs = b.CreateGEP(i8, basearg, funcrva64);
        Value* namervaptr = b.CreateGEP(i8, ed, ConstantInt::get(i64, 0x20));
        Value* namerva = b.CreateLoad(i32, namervaptr);
        Value* namerva64 = b.CreateZExt(namerva, i64);
        Value* names = b.CreateGEP(i8, basearg, namerva64);
        Value* ordrvaptr = b.CreateGEP(i8, ed, ConstantInt::get(i64, 0x24));
        Value* ordrva = b.CreateLoad(i32, ordrvaptr);
        Value* ordrva64 = b.CreateZExt(ordrva, i64);
        Value* ords = b.CreateGEP(i8, basearg, ordrva64);
        b.CreateBr(loop);

        b.SetInsertPoint(loop);
        PHINode* iphi = b.CreatePHI(i64, 2, "Index");
        iphi->addIncoming(ConstantInt::get(i64, 0), parse);
        Value* atend = b.CreateICmpUGE(iphi, nn64);
        b.CreateCondBr(atend, notfound, check);

        b.SetInsertPoint(check);
        Value* nameentryptr = b.CreateGEP(i32, names, iphi);
        Value* nameentryrva = b.CreateLoad(i32, nameentryptr);
        Value* nameentryrva64 = b.CreateZExt(nameentryrva, i64);
        Value* nameptr = b.CreateGEP(i8, basearg, nameentryrva64);
        Value* hash = b.CreateCall(h.FnvAscii, {nameptr});
        Value* match = b.CreateICmpEQ(hash, targethash);
        b.CreateCondBr(match, found, advance);

        b.SetInsertPoint(found);
        Value* ordptr = b.CreateGEP(i16, ords, iphi);
        Value* ord16 = b.CreateLoad(i16, ordptr);
        Value* ord64 = b.CreateZExt(ord16, i64);
        Value* funcentryptr = b.CreateGEP(i32, funcs, ord64);
        Value* funcentryrva = b.CreateLoad(i32, funcentryptr);
        Value* funcentryrva64 = b.CreateZExt(funcentryrva, i64);
        Value* func = b.CreateGEP(i8, basearg, funcentryrva64);
        Value* funcint = b.CreatePtrToInt(func, i64);
        Value* edint = b.CreatePtrToInt(ed, i64);
        Value* edendint = b.CreatePtrToInt(edend, i64);
        Value* gelo = b.CreateICmpUGE(funcint, edint);
        Value* lthi = b.CreateICmpULT(funcint, edendint);
        Value* isfwd = b.CreateAnd(gelo, lthi);
        BasicBlock* returnfunc = BasicBlock::Create(c, "ReturnFunc", h.FindExport);
        b.CreateCondBr(isfwd, notfound, returnfunc);

        b.SetInsertPoint(returnfunc);
        b.CreateRet(func);

        b.SetInsertPoint(advance);
        Value* inxt = b.CreateAdd(iphi, ConstantInt::get(i64, 1));
        iphi->addIncoming(inxt, advance);
        b.CreateBr(loop);

        b.SetInsertPoint(notfound);
        b.CreateRet(ConstantPointerNull::get(ptrty));
    }

    {
        FunctionType* ft = FunctionType::get(voidt, {ptrty, ptrty}, false);
        h.Patch = Function::Create(ft, GlobalValue::InternalLinkage, "ImpMimicPatch", m);
        h.Patch->addFnAttr(Attribute::NoInline);
        h.Patch->addFnAttr(Attribute::UWTable);

        Argument* targetarg = h.Patch->getArg(0);
        Argument* disparg = h.Patch->getArg(1);

        BasicBlock* entry = BasicBlock::Create(c, "Entry", h.Patch);
        BasicBlock* targetok = BasicBlock::Create(c, "TargetOk", h.Patch);
        BasicBlock* vprotectok = BasicBlock::Create(c, "VProtectOk", h.Patch);
        BasicBlock* vprotectfail = BasicBlock::Create(c, "VProtectFail", h.Patch);

        // cover may live in a dll that isn't mapped yet; VirtualProtect(null,...) + write would hit address 0, so early-return keeps the guard at 0 for retry
        IRBuilder<> b(entry);
        Value* targetnull = b.CreateICmpEQ(targetarg, ConstantPointerNull::get(ptrty));
        b.CreateCondBr(targetnull, vprotectfail, targetok);

        b.SetInsertPoint(targetok);
        uint64_t kernel32hash = Fnv1aAsciiLower("kernel32.dll");
        uint64_t vprotecthash = Fnv1a64("VirtualProtect");
        Value* kernel32base = b.CreateCall(h.FindModule, {ConstantInt::get(i64, kernel32hash)});
        Value* vprotect = b.CreateCall(h.FindExport, {kernel32base, ConstantInt::get(i64, vprotecthash)});
        Value* vprotectnull = b.CreateICmpEQ(vprotect, ConstantPointerNull::get(ptrty));
        b.CreateCondBr(vprotectnull, vprotectfail, vprotectok);

        b.SetInsertPoint(vprotectfail);
        b.CreateRetVoid();

        b.SetInsertPoint(vprotectok);
        AllocaInst* oldprot = b.CreateAlloca(i32);
        AllocaInst* scratch = b.CreateAlloca(i32);
        oldprot->setAlignment(Align(4));
        scratch->setAlignment(Align(4));
        FunctionType* vprotectft = FunctionType::get(i32, {ptrty, i64, i32, ptrty}, false);
        b.CreateCall(vprotectft, vprotect, {targetarg, ConstantInt::get(i64, 16), ConstantInt::get(i32, 0x40), oldprot});
        b.CreateStore(ConstantInt::get(i8, 0x48), targetarg);
        Value* p1 = b.CreateGEP(i8, targetarg, ConstantInt::get(i64, 1));
        b.CreateStore(ConstantInt::get(i8, 0xB8), p1);
        Value* p2 = b.CreateGEP(i8, targetarg, ConstantInt::get(i64, 2));
        Value* dispint = b.CreatePtrToInt(disparg, i64);
        auto* dispstore = b.CreateStore(dispint, p2);
        dispstore->setAlignment(Align(1));
        Value* p10 = b.CreateGEP(i8, targetarg, ConstantInt::get(i64, 10));
        b.CreateStore(ConstantInt::get(i8, 0xFF), p10);
        Value* p11 = b.CreateGEP(i8, targetarg, ConstantInt::get(i64, 11));
        b.CreateStore(ConstantInt::get(i8, 0xE0), p11);
        Value* oldval = b.CreateLoad(i32, oldprot);
        b.CreateCall(vprotectft, vprotect, {targetarg, ConstantInt::get(i64, 16), oldval, scratch});
        b.CreateRetVoid();
    }

    {
        FunctionType* ft = FunctionType::get(voidt, {ptrty, ptrty}, false);
        h.PatchIat = Function::Create(ft, GlobalValue::InternalLinkage, "ImpMimicPatchIat", m);
        h.PatchIat->addFnAttr(Attribute::NoInline);
        h.PatchIat->addFnAttr(Attribute::UWTable);

        Argument* slotarg = h.PatchIat->getArg(0);
        Argument* valarg = h.PatchIat->getArg(1);

        BasicBlock* entry = BasicBlock::Create(c, "Entry", h.PatchIat);
        BasicBlock* slotok = BasicBlock::Create(c, "SlotOk", h.PatchIat);
        BasicBlock* vprotectok = BasicBlock::Create(c, "VProtectOk", h.PatchIat);
        BasicBlock* vprotectfail = BasicBlock::Create(c, "VProtectFail", h.PatchIat);

        IRBuilder<> b(entry);
        Value* slotnull = b.CreateICmpEQ(slotarg, ConstantPointerNull::get(ptrty));
        b.CreateCondBr(slotnull, vprotectfail, slotok);

        b.SetInsertPoint(slotok);
        uint64_t kernel32hash = Fnv1aAsciiLower("kernel32.dll");
        uint64_t vprotecthash = Fnv1a64("VirtualProtect");
        Value* kernel32base = b.CreateCall(h.FindModule, {ConstantInt::get(i64, kernel32hash)});
        Value* vprotect = b.CreateCall(h.FindExport, {kernel32base, ConstantInt::get(i64, vprotecthash)});
        Value* vprotectnull = b.CreateICmpEQ(vprotect, ConstantPointerNull::get(ptrty));
        b.CreateCondBr(vprotectnull, vprotectfail, vprotectok);

        b.SetInsertPoint(vprotectfail);
        b.CreateRetVoid();

        b.SetInsertPoint(vprotectok);
        AllocaInst* oldprot = b.CreateAlloca(i32);
        AllocaInst* scratch = b.CreateAlloca(i32);
        oldprot->setAlignment(Align(4));
        scratch->setAlignment(Align(4));
        FunctionType* vprotectft = FunctionType::get(i32, {ptrty, i64, i32, ptrty}, false);
        b.CreateCall(vprotectft, vprotect, {slotarg, ConstantInt::get(i64, 8), ConstantInt::get(i32, 0x04), oldprot});
        auto* st = b.CreateStore(valarg, slotarg);
        st->setAlignment(Align(8));
        Value* oldval = b.CreateLoad(i32, oldprot);
        b.CreateCall(vprotectft, vprotect, {slotarg, ConstantInt::get(i64, 8), oldval, scratch});
        b.CreateRetVoid();
    }
}

static void EnsureCoverDefaultLibs(Module& m)
{
    static const char* coverlibs[] = {
        "kernel32.lib", "user32.lib", "advapi32.lib", "shell32.lib",
        "ole32.lib", "oleaut32.lib", "gdi32.lib", "shlwapi.lib",
    };
    LLVMContext& c = m.getContext();
    NamedMDNode* nmd = m.getOrInsertNamedMetadata("llvm.linker.options");

    DenseSet<StringRef> have;
    for (unsigned i = 0, n = nmd->getNumOperands(); i < n; ++i)
    {
        MDNode* op = nmd->getOperand(i);
        if (op && op->getNumOperands() > 0)
            if (auto* s = dyn_cast<MDString>(op->getOperand(0)))
                have.insert(s->getString());
    }

    for (const char* lib : coverlibs)
    {
        std::string arg = std::string("/DEFAULTLIB:") + lib;
        if (have.contains(arg)) continue;
        MDString* argmd = MDString::get(c, arg);
        MDNode* node = MDNode::get(c, {argmd});
        nmd->addOperand(node);
    }
}

static void SetupMimicContext(Module& m, MimicContext& ctx)
{
    LLVMContext& c = m.getContext();
    Type* i64 = Type::getInt64Ty(c);

    EnsureCoverDefaultLibs(m);

    ArrayType* poolty = ArrayType::get(i64, 8);
    ctx.TlsPool = cast<GlobalVariable>(m.getOrInsertGlobal("ImpMimicTls", poolty));
    ctx.TlsPool->setLinkage(GlobalValue::InternalLinkage);
    if (!ctx.TlsPool->hasInitializer()) ctx.TlsPool->setInitializer(ConstantAggregateZero::get(poolty));
    ctx.TlsPool->setThreadLocal(true);
    ctx.TlsPool->setAlignment(Align(16));

    CreateMimicHelpers(m, ctx.Helpers);

    ctx.EntropyGV = cast<GlobalVariable>(m.getOrInsertGlobal("ImpMimicEntropy", i64));
    ctx.EntropyGV->setLinkage(GlobalValue::PrivateLinkage);
    if (!ctx.EntropyGV->hasInitializer()) ctx.EntropyGV->setInitializer(ConstantInt::get(i64, 0));
    ctx.EntropyGV->setConstant(false);

    unsigned seed = (unsigned)std::chrono::high_resolution_clock::now().time_since_epoch().count();
    ctx.Rng.seed(seed);
}

static Function* CreateDispatcher(Module& m, unsigned siteid, FunctionType* siteft, uint64_t cookieval, const std::vector<unsigned>& perm, const std::vector<uint64_t>& argmasks, const std::vector<StashSlotInfo>& stashinfo, GlobalVariable* tlspool, GlobalVariable* realtargetgv, GlobalVariable* prevhookgv, GlobalVariable* entropygv, std::mt19937_64& rng)
{
    LLVMContext& c = m.getContext();
    Type* i64 = Type::getInt64Ty(c);
    Type* ptrty = PointerType::get(c, 0);

    std::string name = "ImpMimicDispatch" + std::to_string(siteid);
    Function* fn = Function::Create(siteft, GlobalValue::InternalLinkage, name, m);
    fn->setCallingConv(CallingConv::C);
    fn->addFnAttr(Attribute::NoInline);
    fn->addFnAttr(Attribute::UWTable);
    fn->addFnAttr("impmimic-dispatcher");

    BasicBlock* entry = BasicBlock::Create(c, "Entry", fn);
    BasicBlock* owned = BasicBlock::Create(c, "Owned", fn);
    BasicBlock* passthrough = BasicBlock::Create(c, "Passthrough", fn);

    ArrayType* poolty = cast<ArrayType>(tlspool->getValueType());
    Constant* zero64 = ConstantInt::get(i64, 0);

    {
        IRBuilder<> b(entry);
        Value* cookiegep = b.CreateInBoundsGEP(poolty, tlspool, {zero64, zero64});
        Value* cookie = b.CreateLoad(i64, cookiegep);
        Value* match = b.CreateICmpEQ(cookie, ConstantInt::get(i64, cookieval));
        b.CreateCondBr(match, owned, passthrough);
    }

    const unsigned nparams = siteft->getNumParams();
    const unsigned nstash = ChooseStashCount(nparams);

    {
        IRBuilder<> b(owned);
        SmallVector<Value*, 8> realargs;

        // without the volatile marker on the entropy load, llvm folds through it and the plaintext string emerges as a constant
        Value* keydiffadd = nullptr;
        for (unsigned i = 0; i < nstash; ++i)
        {
            if (stashinfo[i].IsString)
            {
                auto* vl = b.CreateLoad(i64, entropygv, "ImpMimicRuntimeZero");
                vl->setVolatile(true);
                keydiffadd = vl;
                break;
            }
        }

        for (unsigned i = 0; i < nstash; ++i)
        {
            Type* pt = siteft->getParamType(i);
            Value* coerced;

            if (stashinfo[i].IsString)
            {
                const auto& pb = stashinfo[i].PlaintextBytes;
                unsigned nbytes = (unsigned)pb.size();
                unsigned nchunks = (nbytes + 7) / 8;

                AllocaInst* slot = b.CreateAlloca(i64, ConstantInt::get(i64, nchunks), "ImpMimicStringSlot");
                slot->setAlignment(Align(8));

                for (unsigned chidx = 0; chidx < nchunks; ++chidx)
                {
                    uint64_t plain = 0;
                    for (unsigned k = 0; k < 8; ++k)
                    {
                        unsigned idx = chidx * 8 + k;
                        if (idx >= nbytes) break;
                        plain |= ((uint64_t)pb[idx]) << (k * 8);
                    }
                    uint64_t mask = rng();
                    uint64_t cipherct = plain + mask;
                    Value* effmask = b.CreateAdd(ConstantInt::get(i64, mask), keydiffadd, "ImpMimicEffMask");
                    Value* dec = b.CreateSub(ConstantInt::get(i64, cipherct), effmask, "ImpMimicDec");
                    Value* dstgep = b.CreateInBoundsGEP(i64, slot, ConstantInt::get(i64, chidx));
                    b.CreateStore(dec, dstgep);
                }
                coerced = slot;
            }
            else
            {
                Value* gep = b.CreateInBoundsGEP(poolty, tlspool, {zero64, ConstantInt::get(i64, perm[i])});
                Value* raw = b.CreateLoad(i64, gep);
                Value* dec = b.CreateXor(raw, ConstantInt::get(i64, argmasks[i]));
                if (pt->isIntegerTy())
                {
                    unsigned bw = pt->getIntegerBitWidth();
                    if (bw == 64) coerced = dec;
                    else if (bw < 64) coerced = b.CreateTrunc(dec, pt);
                    else coerced = b.CreateZExt(dec, pt);
                }
                else if (pt->isPointerTy())
                {
                    coerced = b.CreateIntToPtr(dec, pt);
                }
                else
                {
                    coerced = b.CreateBitCast(dec, pt);
                }
            }
            realargs.push_back(coerced);
        }
        for (unsigned i = nstash; i < nparams; ++i) realargs.push_back(fn->getArg(i));

        Value* realfp = b.CreateLoad(ptrty, realtargetgv);
        CallInst* call = b.CreateCall(siteft, realfp, realargs);
        call->setCallingConv(CallingConv::C);
        // musttail is incompatible with passing addresses of dispatcher local allocas; skip musttail when any slot is a string
        bool anystring = false;
        for (const auto& s : stashinfo) if (s.IsString) { anystring = true; break; }
        if (!anystring) call->setTailCallKind(CallInst::TCK_MustTail);
        if (siteft->getReturnType()->isVoidTy()) b.CreateRetVoid();
        else b.CreateRet(call);
    }

    {
        // cookie-mismatch must route through the slot's pre-patch value (snapshotted at install time); routing to realtargetgv would misdirect unrelated callers sharing our iat (stl, crt helpers, static libs) to the sensitive target with their own args
        IRBuilder<> b(passthrough);
        Value* prevfp = b.CreateLoad(ptrty, prevhookgv);
        SmallVector<Value*, 8> passargs;
        for (unsigned i = 0; i < nparams; ++i) passargs.push_back(fn->getArg(i));
        CallInst* passcall = b.CreateCall(siteft, prevfp, passargs);
        passcall->setCallingConv(CallingConv::C);
        passcall->setTailCallKind(CallInst::TCK_MustTail);
        if (siteft->getReturnType()->isVoidTy()) b.CreateRetVoid();
        else b.CreateRet(passcall);
    }

    return fn;
}

static void PopulateInstaller(Module& m, Function* fn, const std::string& realdll, const std::string& realapi, GlobalVariable* coveriatslot, Function* dispatcherfn, GlobalVariable* realtargetgv, GlobalVariable* prevhookgv, GlobalVariable* guardgv, MimicContext& ctx)
{
    LLVMContext& c = m.getContext();
    Type* i64 = Type::getInt64Ty(c);
    Type* i8 = Type::getInt8Ty(c);
    PointerType* ptrty = PointerType::get(c, 0);

    BasicBlock* entry = BasicBlock::Create(c, "Entry", fn);
    BasicBlock* checkbase = BasicBlock::Create(c, "CheckBase", fn);
    BasicBlock* checkaddr = BasicBlock::Create(c, "CheckAddr", fn);
    BasicBlock* ok = BasicBlock::Create(c, "Ok", fn);
    BasicBlock* fail = BasicBlock::Create(c, "Fail", fn);

    IRBuilder<> b(entry);
    Constant* nullp = ConstantPointerNull::get(ptrty);

    uint64_t realdllhash = Fnv1aAsciiLower(realdll);
    uint64_t realapihash = Fnv1a64(realapi.c_str());

    Value* realbase = b.CreateCall(ctx.Helpers.FindModule, {ConstantInt::get(i64, realdllhash)});
    b.CreateCondBr(b.CreateICmpEQ(realbase, nullp), fail, checkbase);

    b.SetInsertPoint(checkbase);
    Value* realaddr = b.CreateCall(ctx.Helpers.FindExport, {realbase, ConstantInt::get(i64, realapihash)});
    b.CreateCondBr(b.CreateICmpEQ(realaddr, nullp), fail, checkaddr);

    b.SetInsertPoint(checkaddr);
    // snapshot the iat slot's current value BEFORE patching so the dispatcher's pass through has somewhere to forward unrelated callers; after patchiat the slot holds our dispatcher and reading it would self loop
    Value* prevval = b.CreateLoad(ptrty, coveriatslot);
    b.CreateStore(prevval, prevhookgv);
    b.CreateStore(realaddr, realtargetgv);
    b.CreateCall(ctx.Helpers.PatchIat, {coveriatslot, dispatcherfn});
    b.CreateBr(ok);

    b.SetInsertPoint(ok);
    b.CreateStore(ConstantInt::get(i8, 1), guardgv);
    b.CreateRetVoid();

    b.SetInsertPoint(fail);
    b.CreateRetVoid();
}

static bool ResolveSiteRealTarget(const SiteRecord& site, std::map<std::string, HostState>& hostcache, std::string& outdll, std::string& outapi)
{
    std::string cname = UnmangleCName(site.Callee->getName());
    for (unsigned s = 0; s < SeedHostPoolSize; ++s)
    {
        const std::string host = SeedHostPool[s];
        auto it = hostcache.find(host);
        if (it == hostcache.end())
        {
            HostState hs;
            SourceHost(host, hs);
            it = hostcache.emplace(host, std::move(hs)).first;
        }
        if (!it->second.Sourced) continue;
        if (!it->second.Exports.NameToIndex.count(cname)) continue;
        std::string termhost;
        uint32_t termrva = 0;
        if (ResolveImport(host, cname, hostcache, termhost, termrva))
        {
            outdll = termhost;
            outapi = cname;
            return true;
        }
    }
    return false;
}

static CoverRecord* PickCover(std::vector<CoverRecord>& covers, DenseSet<unsigned>& usedidx, MimicContext& ctx)
{
    const unsigned total = (unsigned)covers.size();
    if (usedidx.size() >= total) return nullptr;

    unsigned start = (unsigned)(ctx.Rng() % total);

    for (unsigned step = 0; step < total; ++step)
    {
        unsigned idx = (start + step) % total;
        if (usedidx.contains(idx)) continue;
        if (!covers[idx].Loaded) continue;
        usedidx.insert(idx);
        return &covers[idx];
    }
    for (unsigned step = 0; step < total; ++step)
    {
        unsigned idx = (start + step) % total;
        if (usedidx.contains(idx)) continue;
        usedidx.insert(idx);
        return &covers[idx];
    }
    return nullptr;
}

static bool RewriteSite(Module& m, SiteRecord& site, Function* coverdecl, const std::vector<unsigned>& perm, const std::vector<uint64_t>& argmasks, const std::vector<StashSlotInfo>& stashinfo, GlobalVariable* tlspool, uint64_t cookieval, MimicContext& ctx)
{
    LLVMContext& c = m.getContext();
    Type* i64 = Type::getInt64Ty(c);

    CallInst* origcall = dyn_cast<CallInst>(site.Call);
    if (!origcall) return false;

    SmallVector<Value*, 8> origargs;
    for (Value* a : origcall->args()) origargs.push_back(a);
    FunctionType* siteft = origcall->getFunctionType();
    const unsigned nparams = siteft->getNumParams();
    const unsigned nstash = ChooseStashCount(nparams);

    BasicBlock* bb = origcall->getParent();
    BasicBlock* coverbb = bb->splitBasicBlock(origcall, "ImpMimicCover");

    BasicBlock::iterator aftercall = ++origcall->getIterator();
    BasicBlock* postbb = coverbb->splitBasicBlock(&*aftercall, "ImpMimicPost");
    (void)postbb;

    ArrayType* poolty = cast<ArrayType>(tlspool->getValueType());
    Constant* zero64 = ConstantInt::get(i64, 0);

    {
        IRBuilder<> b(origcall);

        Value* cookiegep = b.CreateInBoundsGEP(poolty, tlspool, {zero64, zero64});
        b.CreateStore(ConstantInt::get(i64, cookieval), cookiegep);

        // string slots skip tls entirely; dispatcher gets plaintext from baked `cipher_ct` immediates in its own ir so the site shows no decrypt sequence
        for (unsigned i = 0; i < nstash; ++i)
        {
            if (stashinfo[i].IsString) continue;

            Value* arg = origargs[i];
            Type* at = arg->getType();
            Value* raw;
            if (at->isIntegerTy())
            {
                unsigned bw = at->getIntegerBitWidth();
                if (bw == 64) raw = arg;
                else if (bw < 64) raw = b.CreateZExt(arg, i64);
                else raw = b.CreateTrunc(arg, i64);
            }
            else if (at->isPointerTy())
            {
                raw = b.CreatePtrToInt(arg, i64);
            }
            else
            {
                raw = b.CreateBitCast(arg, i64);
            }
            Value* enc = b.CreateXor(raw, ConstantInt::get(i64, argmasks[i]));
            Value* gep = b.CreateInBoundsGEP(poolty, tlspool, {zero64, ConstantInt::get(i64, perm[i])});
            b.CreateStore(enc, gep);
        }

        SmallVector<Value*, 8> coverargs;
        for (unsigned i = 0; i < nparams; ++i)
        {
            if (i < nstash)
            {
                uint64_t decoyval = ctx.Rng();
                Type* pt = siteft->getParamType(i);
                Value* dec;
                if (pt->isIntegerTy())
                {
                    unsigned bw = pt->getIntegerBitWidth();
                    uint64_t masked = (bw >= 64) ? decoyval : (decoyval & ((1ULL << bw) - 1));
                    dec = ConstantInt::get(pt, masked);
                }
                else if (pt->isPointerTy())
                {
                    dec = ConstantExpr::getIntToPtr(ConstantInt::get(i64, decoyval), pt);
                }
                else
                {
                    dec = Constant::getNullValue(pt);
                }
                coverargs.push_back(dec);
            }
            else
            {
                coverargs.push_back(origargs[i]);
            }
        }

        CallInst* newcall = b.CreateCall(siteft, coverdecl, coverargs);
        newcall->setCallingConv(origcall->getCallingConv());
        if (!origcall->getType()->isVoidTy())
        {
            newcall->takeName(origcall);
            origcall->replaceAllUsesWith(newcall);
        }

        IRBuilder<> b2(newcall->getNextNode());
        Value* clrgep = b2.CreateInBoundsGEP(poolty, tlspool, {zero64, zero64});
        b2.CreateStore(ConstantInt::get(i64, 0), clrgep);

        origcall->eraseFromParent();
        site.Call = newcall;
    }

    return true;
}

static bool TransformSites(Module& m, std::vector<SiteRecord>& sites, std::vector<CoverRecord>& covers)
{
    if (sites.empty() || covers.empty()) return false;

    LLVMContext& c = m.getContext();
    MimicContext ctx;
    SetupMimicContext(m, ctx);

    DenseSet<Function*> eligibleset;
    BuildEligibleSet(m, eligibleset);

    DenseSet<uint64_t> seen;
    std::vector<CoverRecord> workcovers;
    workcovers.reserve(covers.size());
    for (const CoverRecord& cr : covers)
    {
        uint64_t h = Fnv1a64(cr.Name.c_str());
        if (seen.insert(h).second) workcovers.push_back(cr);
    }
    DenseSet<unsigned> usedcoveridx;

    std::map<std::string, HostState> hostcache;

    Type* ptrty = PointerType::get(c, 0);
    Type* i8 = Type::getInt8Ty(c);

    bool mutated = false;

    for (SiteRecord& site : sites)
    {
        unsigned siteid = ctx.NextSiteId++;
        CallInst* ci = dyn_cast<CallInst>(site.Call);
        if (!ci) continue;
        FunctionType* siteft = ci->getFunctionType();
        unsigned nparams = siteft->getNumParams();

        if (nparams > 8) continue;

        std::string realdll, realapi;
        if (!ResolveSiteRealTarget(site, hostcache, realdll, realapi)) continue;

        CoverRecord* cover = PickCover(workcovers, usedcoveridx, ctx);
        if (!cover) continue;

        unsigned nstash = ChooseStashCount(nparams);
        std::vector<unsigned> perm = GenTlsPermutation(ctx.Rng, nstash);
        std::vector<uint64_t> argmasks = GenArgMasks(ctx.Rng, nstash);

        std::vector<StashSlotInfo> stashinfo(nstash);
        for (unsigned s = 0; s < nstash; ++s)
        {
            Value* arg = ci->getArgOperand(s);
            unsigned bytelen = 0;
            bool iswide = false;
            GlobalVariable* strgv = GetStringLiteralGV(arg, bytelen, iswide);
            if (!strgv) continue;
            auto* cds = cast<ConstantDataSequential>(strgv->getInitializer());
            StringRef raw = cds->getRawDataValues();
            stashinfo[s].IsString = true;
            stashinfo[s].ByteLen = bytelen;
            stashinfo[s].PlaintextBytes.assign(raw.begin(), raw.end());
        }
        uint64_t cookieval = ctx.Rng();
        if (cookieval == 0) cookieval = 0xA5A5A5A5DEADBEEFULL;

        Function* coverdecl = m.getFunction(cover->Name);
        if (coverdecl) continue;
        coverdecl = Function::Create(siteft, GlobalValue::ExternalLinkage, cover->Name, &m);
        coverdecl->setDLLStorageClass(GlobalValue::DLLImportStorageClass);
        coverdecl->setCallingConv(ci->getCallingConv());

        std::string impname = std::string("__imp_") + cover->Name;
        GlobalVariable* iatslot = m.getGlobalVariable(impname);
        if (!iatslot)
        {
            iatslot = new GlobalVariable(m, ptrty, false, GlobalValue::ExternalLinkage, nullptr, impname);
        }

        auto* realtargetgv = new GlobalVariable(m, ptrty, false, GlobalValue::PrivateLinkage, Constant::getNullValue(ptrty), "ImpMimicReal" + std::to_string(siteid));
        // snapshot of the iat slot's original contents (saved by the installer BEFORE patching); dispatcher's cookie mismatch path forwards to this so unrelated callers of the cover (stl / static libs sharing our iat) get the cover's own semantics instead of being misrouted to the sensitive target
        auto* prevhookgv = new GlobalVariable(m, ptrty, false, GlobalValue::PrivateLinkage, Constant::getNullValue(ptrty), "ImpMimicPrev" + std::to_string(siteid));
        auto* guardgv = new GlobalVariable(m, i8, false, GlobalValue::PrivateLinkage, ConstantInt::get(i8, 0), "ImpMimicGuard" + std::to_string(siteid));

        FunctionType* instft = FunctionType::get(Type::getVoidTy(c), {}, false);
        std::string instname = "ImpMimicInstall" + std::to_string(siteid);
        Function* installerfn = Function::Create(instft, GlobalValue::InternalLinkage, instname, m);
        installerfn->addFnAttr(Attribute::NoInline);
        installerfn->addFnAttr(Attribute::UWTable);
        installerfn->addFnAttr("impmimic-installer");

        if (!RewriteSite(m, site, coverdecl, perm, argmasks, stashinfo, ctx.TlsPool, cookieval, ctx))
        {
            installerfn->eraseFromParent();
            realtargetgv->eraseFromParent();
            prevhookgv->eraseFromParent();
            guardgv->eraseFromParent();
            continue;
        }

        Function* dispatcherfn = CreateDispatcher(m, siteid, siteft, cookieval, perm, argmasks, stashinfo, ctx.TlsPool, realtargetgv, prevhookgv, ctx.EntropyGV, ctx.Rng);

        Function* installpoint = site.Caller;
        Function* walked = FindInstallPoint(site.Caller, site.Callee, eligibleset);
        if (walked) installpoint = walked;

        PopulateInstaller(m, installerfn, realdll, realapi, iatslot, dispatcherfn, realtargetgv, prevhookgv, guardgv, ctx);

        AddInstallSequence(installpoint, installerfn, guardgv);

        mutated = true;
    }

    return mutated;
}

bool RunImportMimic(Module& m)
{
    if (!MimicEnable) return false;

    std::vector<SiteRecord> sites;
    std::vector<CoverRecord> covers;

    for (Function& f : m)
    {
        if (f.isDeclaration()) continue;

        bool veto = HasNoImpMimicAnnotation(f);
        bool opt = HasImpMimicAnnotation(f);
        if (veto) continue;
        if (!opt) continue;

        for (BasicBlock& bb : f)
        {
            for (Instruction& i : bb)
            {
                auto* cb = dyn_cast<CallBase>(&i);
                if (!cb) continue;

                Function* callee = nullptr;
                if (!ClassifySite(cb, callee)) continue;

                SiteRecord rec;
                rec.Call = cb;
                rec.Caller = &f;
                rec.Callee = callee;
                rec.ArgCount = callee->getFunctionType()->getNumParams();
                sites.push_back(rec);
            }
        }
    }

    DenseSet<uint64_t> moduleimporthashes;
    for (Function& f : m)
    {
        if (!IsImportDecl(&f)) continue;
        std::string cname = UnmangleCName(f.getName());
        moduleimporthashes.insert(Fnv1a64(cname.c_str()));
    }

    std::vector<std::string> loadeddlls = DiscoverImportedDlls(m);
    for (auto& d : loadeddlls) d = ToLowerAscii(d);
    std::vector<std::string> extradlls = ParseDllList(ExtraDllsDefault);

    struct PoolEntry
    {
        std::string Dll;
        bool Loaded;
    };
    std::vector<PoolEntry> dllpool;
    DenseSet<uint64_t> seenpool;
    auto addpool = [&](const std::string& d, bool loaded)
    {
        uint64_t h = Fnv1a64(d.c_str());
        if (!seenpool.insert(h).second) return;
        dllpool.push_back({d, loaded});
    };
    for (const auto& d : loadeddlls) addpool(d, true);
    for (const auto& d : extradlls) addpool(d, false);

    std::map<std::string, HostState> hostcache;

    for (const PoolEntry& pe : dllpool)
    {
        const std::string& dll = pe.Dll;

        auto it = hostcache.find(dll);
        if (it == hostcache.end())
        {
            HostState hs;
            SourceHost(dll, hs);
            it = hostcache.emplace(dll, std::move(hs)).first;
        }
        if (!it->second.Sourced) continue;

        const DLLExportGrabber::ExportTable& t = it->second.Exports;
        for (const auto& nameidx : t.NameToIndex)
        {
            const std::string& name = nameidx.first;
            const size_t idx = nameidx.second;
            if (idx >= t.Entries.size()) continue;
            const DLLExportGrabber::ExportEntry& e = t.Entries[idx];

            const uint64_t h = Fnv1a64(name.c_str());
            if (moduleimporthashes.contains(h)) continue;

            if (IsCoverCompilerHelper(name)) continue;
            if (IsCoverCrtExcluded(name)) continue;

            // named forwarders (DLL.FunctionName) make find_export return the forwarder-string address inside .rdata; hooking there faults DEP on first call
            if (e.Forwarded) continue;

            if (!IsSafeCoverName(name)) continue;

            CoverRecord cr;
            cr.Name = name;
            cr.Dll = dll;
            cr.HashedName = h;
            cr.Loaded = pe.Loaded;
            covers.push_back(cr);
        }
    }

    return TransformSites(m, sites, covers);
}

PreservedAnalyses ImportMimicPass::run(Module& m, ModuleAnalysisManager&)
{
    bool mutated = RunImportMimic(m);
    return mutated ? PreservedAnalyses::none() : PreservedAnalyses::all();
}