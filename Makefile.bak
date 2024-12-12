all:
	happy -gca UniSyn/Par.y
	alex -g UniSyn/Lex.x
	ghc --make UniSyn/Test.hs -o UniSyn/Test

clean:
	-rm -f UniSyn/*.log UniSyn/*.aux UniSyn/*.hi UniSyn/*.o UniSyn/*.dvi

distclean: clean
	-rm -f UniSyn/Doc.* UniSyn/Lex.* UniSyn/Par.* UniSyn/Layout.* UniSyn/Skel.* UniSyn/Print.* UniSyn/Test.* UniSyn/Abs.* UniSyn/Test UniSyn/ErrM.* UniSyn/SharedString.* UniSyn/ComposOp.* UniSyn/UniSyn.dtd UniSyn/XML.* Makefile*
		-rmdir -p UniSyn/

