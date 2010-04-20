XSL_PASS_1 = gappa.xml gappa-preprocess.xsl $(wildcard manual/*.xml) $(wildcard examples/*.xml)

EXTRA_DIST = $(XSL_PASS_1) gappa-html.xsl gappa.css gappa.sty \
             $(wildcard images/*.png) \
             doxygen/Doxyfile

gappa-preprocessed.xml: $(XSL_PASS_1)
	$(XSLTPROC) -o gappa-preprocessed.xml "$(srcdir)/gappa-preprocess.xsl" "$(srcdir)/gappa.xml"

html-doc: gappa-preprocessed.xml
	rm -rf tmp/ html/
	mkdir html
	java -cp "/usr/share/java/saxon.jar:/usr/share/java/xslthl.jar" com.icl.saxon.StyleSheet gappa-preprocessed.xml gappa-html.xsl
	cp "$(srcdir)/gappa.css" html/
	mkdir html/images
	cp "$(srcdir)/images"/*.png html/images/
	mkdir tmp
	mv tex-math-equations.tex tmp/
	sed -e 's/dvi2bitmap outputfile/dvi2bitmap mark outputfile/' tmp/tex-math-equations.tex > tmp/tex-math-equations.tex.2
	mv tmp/tex-math-equations.tex.2 tmp/tex-math-equations.tex
	cd tmp ; latex tex-math-equations.tex
	cd tmp ; $(DVI2BITMAP) --magnification=4 --scaledown=4 --verbose=quiet --query=bitmaps tex-math-equations.dvi |\
	  awk '$$6 > -10 {printf "s/img src=\"%s\"/img style=\"margin-bottom: %dpx\" src=\"%s\"/g\n", $$2, ($$6 - $$4 + 14.25), $$2}' > margin.sed
	for f in html/*.html; do sed -f tmp/margin.sed "$$f" > "$$f.2"; mv "$$f.2" "$$f"; done
	mv tmp/*.png html/
	rm -rf tmp/

pdf-doc: gappa-preprocessed.xml
	dblatex -P latex.class.options=twoside -P ulink.show=1 -P ulink.footnotes=1 -s gappa -o gappa.pdf gappa-preprocessed.xml

clean-local:
	rm -rf gappa.pdf html/
