
A demo for dumping Core so that one can actually see the order these executions are happening




Change the follwing accordngly:

To build

```
bapbuild comment.plugin
bapbundle install comment.plugin
```

You can then see the theory is enabled

```
bap list theories
```

You can see the slot we've created for comments by looking at

```
bap list classes | grep comment
```

These comments can be seen in the knowledge base

```
gcc main.c
bap a.out -dknowledge | grep hello
```

Discussion:
https://gitter.im/BinaryAnalysisPlatform/bap?at=6182dfeffb8ca0572bfed24e