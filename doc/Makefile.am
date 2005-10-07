EXTRA_DIST = gappa.xml gappa-preprocess.xsl gappa.xsl gappa.css manual/*.xml examples/*.xml

html-doc: clean-local
	$(XSLTPROC) -o gappa-preprocessed.xml "$(srcdir)/gappa-preprocess.xsl" "$(srcdir)/gappa.xml"
	$(XSLTPROC) -o html/ "$(srcdir)/gappa.xsl" gappa-preprocessed.xml
	rm gappa-preprocessed.xml
	cp "$(srcdir)/gappa.css" html/
	sed -e 's/dvi2bitmap outputfile/dvi2bitmap mark outputfile/' -i html/tex-math-equations.tex
	mkdir html/tmp
	mv html/tex-math-equations.tex html/tmp/
	cd html/tmp ; latex tex-math-equations.tex
	cd html/tmp ; $(DVI2BITMAP) --magnification=4 --scaledown=4 --verbose=quiet --query=bitmaps tex-math-equations.dvi |\
	  awk '$$6 > -10 {printf "s/img src=\"%s\"/img style=\"margin-bottom: %dpx\" src=\"%s\"/g\n", $$2, ($$6 - $$4 + 14.25), $$2}' > margin.sed
	for f in html/*.html; do sed -f html/tmp/margin.sed -i "$$f"; done
	mv html/tmp/*.png html/
	rm -rf html/tmp/

clean-local:
	rm -rf html/
