# Import Mimicking Pass
Built for LLVM 19.1 - Windows x64 <br> <br>

This pass is quite simple, the idea is to just a different twist on import obfuscation, most techniques are basic lazy imports, we are in all intensive purposes also lazy importing; just with a misdirection using hooks to load. <br>
Instead of just walking the export table and indirect calling modbase + exportrva, we instead set a fake call up to an unused import at the site.  <br>
Before the fake import is called we resolve the real one and then place a hook on it, this hook is thread safe, checking the RVA and supporting multi function hooking on the import. <br>
To anyone statically analysing the code without proper care and without interrogating each hook, they see false imports. <br>
This also allows us to hide the actual import parameters. As the parameters are 


## The Methodology
* First of all we set up the EAT walk for the lazy import, Finding the exported module.
* We then set up the return RVA mechanism so we can have multiple different hooks handles.
* We then set up the parameter encryption
* Then finally the hook onto the actual import
* Then at function call to the fake function we pass the encrypted parameters over TLS
* Then invoke the hooked import, which will then resolve through the hook tree and decrypt the parameters and indirect call the real import.

Hook setup:<br>
<img width="285" height="744" alt="image" src="https://github.com/user-attachments/assets/943af46b-5f19-4bf0-9cb3-b1a8efc5d9e4" />


<img width="500" height="285" alt="image" src="https://github.com/user-attachments/assets/f5f71bb4-bf5e-4965-b319-c5eb4c827d6e" />

Fake invoke: <br>
<img width="725" height="143" alt="image" src="https://github.com/user-attachments/assets/78885114-a880-4e16-8239-1117a4fee7e8" />

If you are intentive, you will notice we directly reference the import in the hook. Yeah thats my bad, you might want to fix that(grab it from EAT walk, the same way you lazy import) if you use this. I have no usage for it though. <br>


## Annotations
```c
__attribute__((annotate("impmimic")))
``` 
* Applies protection to imports

## How To Build
* Download [LLVM 19.1](https://github.com/llvm/llvm-project/releases/tag/llvmorg-19.1.0)
* Download [VCPKG](https://github.com/microsoft/vcpkg)
* VCPKG install asmjit
* Open build.bat in a text editor.
* Find the LLVM 19.1 references in the command line, Change them to your file path.
* Find the VCPKG references in the command line, Change them to your file path.
* Run the build script
* Build your application with the ``` -load-pass-plugin ``` Param to the FunctionPass.dll
