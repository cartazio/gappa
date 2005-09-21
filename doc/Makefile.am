EXTRA_DIST = gappa.xml gappa-preprocess.xsl gappa.xsl gappa.css manual/*.xml examples/*.xml

html-doc:
	$(XSLTPROC) -o gappa-preprocessed.xml "$(srcdir)/gappa-preprocess.xsl" "$(srcdir)/gappa.xml"
	$(XSLTPROC) -o html/ "$(srcdir)/gappa.xsl" gappa-preprocessed.xml
	rm gappa-preprocessed.xml
	cp "$(srcdir)/gappa.css" html/
	mkdir html/tmp
	cd html/tmp ; \
	mv ../tex-math-equations.tex . ; \
	latex tex-math-equations.tex ; \
	$(DVI2BITMAP) --magnification=4 --scaledown=4 tex-math-equations.dvi ; \
	mv *.png ..
	rm -r html/tmp

clean-local:
	rm -rf html/
