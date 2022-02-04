
smt.plugin: smt.ml
	bapbuild smt.plugin
showchc.plugin: showchc.ml
	bapbuild -pkg=bap-primus showchc.plugin

install: smt.plugin showchc.plugin
	bapbundle install smt.plugin
	bapbundle install showchc.plugin