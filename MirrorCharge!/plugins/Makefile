plugin: myocamlbuild.ml
	ocamlbuild mirror-charge.otarget

clean:
	@ ocamlbuild -clean
	@ rm -f myocamlbuild.ml Makefile.paths

myocamlbuild.ml:
	@ ln -s $(COQLIB)user-contrib/PluginUtils/myocamlbuild.ml myocamlbuild.ml

Makefile.paths:
	@ coqc -config > Makefile.paths

include Makefile.paths
