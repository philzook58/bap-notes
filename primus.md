# Primus

Primus is an extensible interpreter. You can use it for fuzzing, symbolic execution, taint tracking, and more.

The pieces of functionality are implemented by components. They can be mixed and matched.

To see the list of available components type

`bap primus-components`

Prepackaged combos of components are called "systems". You can see the available systems by typing

`bap primus-systems`

On my system this returns

```
- bap:constant-tracker:
  Uses promiscuous-executor for constant tracking.

- bap:microexecutor-base:
  The base system for microexecution systems.

- bap:symbolic-executor:
  Uses symbolic execution to analyze all feasible and
  linearly independent paths.

- bap:base-taint-analyzer:
  Uses promiscuous-executor for taint analysis.
  No policy is specified

- bap:binary-executor:
  Executes a binary program.

- bap:taint-analyzer:
  Uses promiscuous-executor for taint analysis.
  The default taint propagation policy is selected
  using the --primus-taint-select-default-policy
  option (defaults to propagate-by-computation)

- bap:reflective-taint-analyzer:
  A taint analyzer that reflects taints to/from BIR terms

- bap:stubbed-executor:
  Executes a binary together with the Lisp Machine

- bap:legacy-main:
  The legacy Primus system that contains all components registered with the
  Machine.add_component function.

- bap:base-lisp-machine:
  Executes Primus Lisp program.

- bap:promiscuous-executor:
  Executes all linearly independent paths and never fails.

- bap:terminating-stubbed-executor:
  Executes a binary together with the Lisp Machine that
  is guaranteed to terminate.

- bap:multi-analyzer:
  Runs several analyses in parallel.

- bap:exact-taint-analyzer:
  Uses promiscuous-executor for taint analysis.
  Propagates taint exactly.

- bap:string-deobfuscator:
  Uses promiscuous-executor to find obfuscated strings.
```

To use primus in the simplest way, you can use the bap `run` plugin. Using the `run` plugin can be confusing because key command line options are supplied to other plugins.





Now try reading the basic documentation of Primus
https://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/index.html


Under the hood, primus is extensible because you can register callbacks to certain events called "observations". This is reminscent of register event listers in a browser for example.

To see the list of available observations type

`bap primus-observations`


## Ocaml

Primus is written as a generic monad transformer. You should ignore that. Do not look in the `Machine` module. You actually want `Analysis.t` which is this monad transformer specialized to the knowledge base monad.

https://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/Primus/Analysis/index.html


## Systems
There is significant descriptive documentation of the primus machine execution cycle in the `System` module. You should read it.
https://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/Primus/System/index.html

You may write `.asd` files to describe systems. `.asd` is borrowed from the common lisp world. You can find the definition of the built in systems here
https://github.com/BinaryAnalysisPlatform/bap/blob/97fb7fa6a8a90faeae2b077d8ad59b8b882d7c32/plugins/primus_systems/systems/core.asd

There is a short tutorial in the wiki here https://github.com/BinaryAnalysisPlatform/bap/wiki/Tutorial:-writing-a-symbolic-taint-analyzer on how to make a new one.

## State

You can add new kinds of state. You need to register the state globally with a unique uuid (it's odd). It looks like this to declare state

```ocaml
let state =
  Primus.Machine.State.declare
    ~name:"unchecked-return-value"
    ~uuid:"7390b60d-fac6-42f7-b13b-94b85bba7586"
    (fun _ -> {addrs = Set.empty (module Addr); verbose=false})
```
## Forking

## Components

To make a component, write a function in the `Analysis.t` monad that registers the callbacks to the events you care about. Pass this `unit Analysis.t` to `Component.register`. That's it.

## Observations

Most observations of interest are in the `Primus.Interprete` module https://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/Primus/Interpreter/index.html

## Linker
It may surprise you that really important functionality is in the `Linker` module.

https://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/Primus/Linker/index.html

