EXTRA_DIST = gappa.xml gappa-preprocess.xsl gappa.xsl gappa.css gappa.dsl unescape_math.pl \
             $(wildcard manual/*.xml) $(wildcard examples/*.xml) $(wildcard images/*.png) \
             doxygen/Doxyfile

html-doc:
	rm -rf tmp/ html/
	mkdir html
	cp "$(srcdir)/gappa.xml" "$(srcdir)"/gappa*.xsl html/
	mkdir html/manual html/examples
	cp "$(srcdir)/manual"/*.xml html/manual/
	cp "$(srcdir)/examples"/*.xml html/examples/
	(cd html/ ; java -cp "/usr/share/java/saxon.jar:/usr/share/java/xslthl.jar" com.icl.saxon.StyleSheet gappa.xml gappa-html.xsl)
	rm -r html/gappa.xml html/gappa*.xsl html/manual/ html/examples/
	cp "$(srcdir)/gappa.css" html/
	mkdir html/images
	cp "$(srcdir)/images"/*.png html/images/
	mkdir tmp
	mv html/tex-math-equations.tex tmp/
	sed -e 's/dvi2bitmap outputfile/dvi2bitmap mark outputfile/' tmp/tex-math-equations.tex > tmp/tex-math-equations.tex.2
	mv tmp/tex-math-equations.tex.2 tmp/tex-math-equations.tex
	cd tmp ; latex tex-math-equations.tex
	cd tmp ; $(DVI2BITMAP) --magnification=4 --scaledown=4 --verbose=quiet --query=bitmaps tex-math-equations.dvi |\
	  awk '$$6 > -10 {printf "s/img src=\"%s\"/img style=\"margin-bottom: %dpx\" src=\"%s\"/g\n", $$2, ($$6 - $$4 + 14.25), $$2}' > margin.sed
	for f in html/*.html; do sed -f tmp/margin.sed "$$f" > "$$f.2"; mv "$$f.2" "$$f"; done
	mv tmp/*.png html/
	rm -rf tmp/

pdf-doc:
	$(XSLTPROC) -o gappa-preprocessed.xml "$(srcdir)/gappa-pdf.xsl" "$(srcdir)/gappa.xml"
	dblatex -P latex.class.options=twoside -P ulink.show=1 -P ulink.footnotes=1 -s gappa -o gappa.pdf gappa-preprocessed.xml
	rm gappa-preprocessed.xml

clean-local:
	rm -rf gappa.pdf html/
