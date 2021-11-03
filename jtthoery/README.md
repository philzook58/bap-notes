To build

```
bapbuild comment.plugin
bapbundle install comment.plugin
```

You can then see the theory is enabled

```
bap list theories
```

In principle this might populate the knowledge base

```
gcc main.c
bap a.out -dknowledge | grep hello
```

https://gitter.im/BinaryAnalysisPlatform/bap?at=6182dfeffb8ca0572bfed24e