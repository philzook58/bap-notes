# bap-notes

Bap, the binary analysis platform is a framework that disassembles binary code in a variety of formats and for a variety of architectures and lifts them into a common representation. It then supplies analysis you may perform and tools with which to build your own custom analysis

It is quite the beast.

To me starting out there was a lot to swallow. First I had to learn Ocaml, second I knew even less about program analysis and binary stuff than I do now.

But maybe these notes may make the road easier for you, dear reader.


## Installing

`opam` is the standard ocaml package manager. Long story short:

```
opam depext --install bap # installs bap and its dependencies
```

More details here <https://github.com/BinaryAnalysisPlatform/bap#from-sources>

## The `bap` command

After installing, if you type `bap` you will get a list of information

Typing `bap` on my system gets me. You should actually take a minute to read this. For serious. The `bap` command line itself is some of the best documentation of what bap has.

```
Usage:
  bap <COMMAND> [<OPTIONS>]

Common options:
  --version                prints the version number and exits;
  --plugin-path <DIR>      adds <DIR> to the plugins search path;
  --logdir <DIR>           creates a log file in <DIR>;
  --recipe <VAL>           extracts command line arguments from the recipe.

Commands:
  objdump                  disassembles and prints a binary using the linear sweep algorithm
  mc                       disassembles a (human readable) string of bytes
  primus-observations      prints a list of Primus observations
  primus-components        prints a list of Primus components
  primus-systems           prints a list of Primus systems
  compare                  compares several alternative versions of the binary with the base
  disassemble              disassembles and analyzes the input file
  print-recipes            prints available recipes
  recipes                  provides commands to manipulate the recipe subsystem
  list                     explores various BAP facilities
  .                        does nothing and prints nothing
  cache                    provides options to control cache size and cache garbage collector
  analyze                  analyses the knowledge base
  eval-lisp                runs the Primus lisp program
  show-lisp                shows the static semantics of Primus Lisp definitions
  primus-lisp-documentation no description provided
  dependencies             outputs program dependencies such as libraries and symbols
  specification            displays information about the binary


Plugins:
  abi                      apply abi information to a project
  analyze                  implements the analyze command
  api                      add parameters to subroutines based on known API
  arm                      the target support package that enables support for the ARM family of
  beagle                   microx powered obfuscated string solver
  bil                      provides bil optimizations
  byteweight               find function starts using Byteweight algorithm
  cache                    provide caching services
  callgraph-collator       compares projects by their callgraphs
  callsites                annotate callsites with subroutine's arguments
  constant-tracker         constant Tracking Analysis based on Primus
  cxxfilt                  provide c++filt based demangler
  demangle                 demangle subroutine names
  dependencies             analyses the binary dependencies
  disassemble              implements the disassemble command
  dump-symbols             dump symbol information as a list of blocks
  elf-loader               read ELF and DWARF formats in a pure OCaml
  flatten                  flattens (unrolls) BIR expressions into a trivial form
  frontc-parser            parse c files with FrontC
  glibc-runtime            enables ad-hoc support for glibc runtime code
  llvm                     provide loader and disassembler using LLVM library
  map-terms                map terms using BML DSL
  mc                       bAP Core Library
  mips                     provide MIPS lifter
  objdump                  this plugin provides a symbolizer based on objdump
  optimization             automatically removes dead code and propagates consts
  phoenix                  output project information in a phoenix format
  powerpc                  provide PowerPC lifter
  primus-dictionary        provides a key-value storage
  primus-exploring         evaluates all machines, prioritizing the least visited
  primus-greedy            evaluates all machines in the DFS order
  primus-limit             ensures termination by limiting Primus machines
  primus-lisp              install and load Primus lisp libraries
  primus-loader            generic program loader for Primus
  primus-mark-visited      registers the bap:mark-visited component
  primus-powerpc           powerpc support package
  primus-print             prints Primus states and observations
  primus-promiscuous       enables the promiscuous mode of execution
  primus-propagate-taint   a compatibility layer between different taint analysis frameworks
  primus-random            provides components for Primus state randomization and controls their
  primus-region            interval sets
  primus-round-robin       evaluates all machines in the BFS order
  primus-symbolic-executor enables symbolic execution in Primus
  primus-systems           loads Primus systems and registers them in the system repository
  primus-taint             a taint analysis control interface
  primus-test              primus Program Testing and Verification Kit
  primus-wandering         evaluates all machines while
  primus-x86               x86 support package
  print                    print project in various formats
  propagate-taint          propagate taints through a program
  raw                      provides a loader for raw binaries
  read-symbols             provides functions addresses and (optionally) names from a
  recipe-command           manipulates bap recipes
  relocatable              extracts symbolic information from the program relocations
  report                   reports program status
  riscv                    provide Riscv target
  run                      a pass that will run a program
  specification            prints the specification of the binary (like readelf)
  ssa                      translates a program into the SSA form
  strings                  find strings of characters
  stub-resolver            identifies functions that are stubs and redirects calls to stubs to
  systemz                  provide Systemz lifter
  taint                    taint specified terms
  thumb                    provide Thumb lifter
  trace                    manage execution traces
  trivial-condition-form   eliminates complex conditionals in branches
  warn-unused              warn about unused results of certain functions
  x86                      provide x86 lifter
```

I have no idea what many of these do. A majority of the commands are just ways to query for available capabilities of different kinds

Here are the highlights in my opinion.
- Commands
  + primus-observations      prints a list of Primus observations
  + primus-components        prints a list of Primus components
  + primus-systems           prints a list of Primus systems
  + list                     explores various BAP facilities. Especially helpful for finding slots in the knowledge base
  + cache                    provides options to control cache size and cache garbage collector
  + analyze                  analyses the knowledge base
  + eval-lisp                runs the Primus lisp program
  + show-lisp                shows the static semantics of Primus Lisp definitions
  + primus-lisp-documentation no description provided

- Plugins
  + print
  + run
  + api
  + primus-lisp

Typing `bap list` on my system gives

```
  entities                 prints this message
  plugins                  installed BAP plugins
  commands                 bap utility commands
  recipes                  installed recipes
  features                 plugin capabilities
  passes                   disassembler passes
  formats                  data output formats
  classes                  knowledge representation classes
  theories                 installed theories
  agents                   knowledge providers
  rules                    knowledge base rules
  collators                project collators (comparators)
```

all of which can be further queries. In particular interest are `bap list theories` and `bap list classes` which are important information about the knowledge base (in particular listing the available "theories" which are like different interpretations or analysis of the code. `classes` lists the registered classes and their slots in the knowledge base, aka interesting fields you can query bap for).

`bap -dbir -dbil -dknowledge -dasm -dcfg` are different options to dump different representations of the code. BIR and BIL are two ba intermediatre representations. `-dknowledge` dumps the knowledge base which is kind of everything bap could figure out about the binary.


`bap --help` is an overwhelming amount of information. Typically you need to try to `grep` for an appropriate keyword. `bap --help | grep -C 10 keyword` will show a context of 10 lines around the found keyword. The keyword I use is often the name of bap plugin from the big list above. 


The `bap` command is the same as `bap disassemble`. The code can be found here <https://github.com/BinaryAnalysisPlatform/bap/tree/97fb7fa6a8a90faeae2b077d8ad59b8b882d7c32/plugins/disassemble>


## Bap equivalents of binutils

`objdump` let's you see various outputs about a binary.
- assembly `-d`
- symbol `-t` or `--syms`
- sections & segments  `-x`

`readelf` has some overlap.


`bap -dasm` is like `objdump -d`

`bap specification` is kind of like `readelf --all`

`bap dependencies` is similar to `ldd` I think.

## Primus

Primus is an extensible interpreter/emulator. It can execute code lifted from binaries.
You may mix and match Primus Components

The simplest way to run it is

`bap /bin/true --run --run-entry-points=main --primus-print-observations=exception,pc-change`

For more options
`bap --help | grep -C 10 run`

For more info see [primus.md]

## Giving Bap C info

In order for bap to recover high level function arguments you can supply a header file.
If you know this plugin is called `api` you can find the options available by 
`bap --help | grep -C 4 api`

- `--api-path=somefolder` where somefolder has a folder called C in it.
- `--api-show`
- `--api-list-paths`

### Saving and restoring the knowledge base
You can have bap save it's info and restore it. `bap a.out -k my_knowledge_base --update` will build a knowledge base. Leaving out `--update` is useful for read only access to the KB. This is used for example with `bap analyze -k my_knowledge_base`, which gives a kind of repl for exploring some pieces (but not all) of the knowledge base. Try typing `help` at the prompt for more info.

### Recipes

Recipes are bundles of command line flags I think. Well, they are at least that. This can save copying ad pasting some huge command a bunch. <https://github.com/BinaryAnalysisPlatform/bap-toolkit>  Has some interesting example recipes

### Interesting Places to Look
- Ivan's gists - https://gist.github.com/ivg
- Tests
- Defining instruction semantics using primus lisp tutorial https://github.com/BinaryAnalysisPlatform/bap/wiki/Defining-instructions-semantics-using-Primus-Lisp-(Tutorial)
- https://github.com/BinaryAnalysisPlatform/bap-toolkit Has examples recipes

# Ocaml Stuff

### Finding Stuff
I use a combination of Merlin, Github Search.

The most interesting folders are `lib` and `plugins`

- https://github.com/ivg/bap/blob/master/lib/bap/bap.mli the bap std library
- https://github.com/ivg/bap/tree/master/lib/bap_types many bap types are actually defined here

### Bap is not a library.

Bap is organized is an extensible kind of decentralized way that I find very confusing. I am constantly tempted to treat it as a library and shoot my foot off.


## Plugins vs Commands vs Passes vs Scripts

There are at least 3 different ways you might extend bap.
### Commands 
Commands do something different than the default bap command at the top level.

### Plugins

> And this is the whole idea of BAP as a framework instead of a library. There are extension points, which enable you to extend bap without having to worry about how to create a project, how to properly find the file, how to specify the architecture and other parameters. You just register a pass that takes a ready project and focus on your analysis instead of writing all this boilerplate. E.g., in the example above it is rightful to assume that you want to get the project before starting enqueing jobs, so you can register a pass that will be called once the project is ready and if the pass is selected,

https://binaryanalysisplatform.github.io/bap/api/master/bap-main/Bap_main/index.html
https://gitter.im/BinaryAnalysisPlatform/bap?at=610c3e322453386b6c373696
https://en.wikipedia.org/wiki/Dependency_injection
Plugins are meant to be mixed and matched. They extend the functionality of other bap commands.

You make plugins by building and installing it

```
bapbuild comment.plugin
bapbundle install comment.plugin
```
Any side effects of setting up the plugin should happen inside an `Extension.declare`. It consistently causes problem that bap requires certain things to happen at certain stages, and if you go off the reservation, you'll probably eat shit.

```
let () =
  Bap_main.Extension.declare (fun _ctx -> dostuff)
```

The stuff you might do might involve declaring new slots in the knowledge base, declaring new interpetations, declaring new primus components, stuff like that.

### Scripts
"Scripts" are a thing I've made up and am not sure are actually recommended. You can make a standalone binary using that call Bap_main.init.
To make a basic file to explore some binary, first make a dune file

```lisp
( executable
  (name main)
  (libraries bap bap-primus)
  (flags -linkall)
  (preprocess (pps ppx_jane))
)
```


```ocaml
open Core_kernel
open Bap.Std
include Self()

(* Must call init before everything*)
let () = match Bap_main.init () with
        | Ok _ -> ()
        | Error s -> failwith s

(* Load a file as a project *)
let myfile = "/home/philip/Documents/ocaml/a.out"
let proj = Project.create (Project.Input.file ~loader:"llvm" ~filename:myfile) |> Or_error.ok_exn

(* Getting the current knowledge base *)
let state = Toplevel.current ()

```

### Registries

A ubiquitous programming pattern in the implementation of bap is to define global level registries for various constructs.

- Plugins
- Commands
- Knowledge Base Classes
- Knowledge Base Slots
- Core Theory implementations
- Primus Components
- Primus Observations

To learn about the contents of these registries, and hence the available capaibilities, the best way is to find the appropriate way to ask the `bap` command line tool. I then use the github search feature on the bap repo to search for a important string in question.