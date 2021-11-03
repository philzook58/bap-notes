

If I make a core theory instance for Sexp.t smtlib
Can i lift using primus lisp-show

I make a plugin that registers a core-theory instance?
Which perhaps -knowledge will do?



building souffle.
We revmoed all the extra flags turned off tests
removed all mentions of libffi
src/CMakeLists.txt - removed werror
CMakeLists.txt

removed ffi.h from interpeter/engine.cpp by removing the entire case

ok the frontend needs a bunch of stuff. It calls mcpp first.
This strips comments maybe?

https://github.com/hoodmane/libffi-emscripten
https://github.com/emscripten-core/emscripten/issues/11066
It's conceviable libffi could be made to work