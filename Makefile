all:
	happy -gca E/Par.y
	alex -g E/Lex.x
	ghc --make E/Test.hs -o E/Test

clean:
	-rm -f E/*.log E/*.aux E/*.hi E/*.o E/*.dvi

distclean: clean
	-rm -f E/Doc.* E/Lex.* E/Par.* E/Layout.* E/Skel.* E/Print.* E/Test.* E/Abs.* E/Test E/ErrM.* E/SharedString.* E/ComposOp.* E/E.dtd E/XML.* Makefile*
		-rmdir -p E/

