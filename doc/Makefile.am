EXTRA_DIST = gappa.xml gappa-preprocess.xsl gappa.xsl gappa.css gappa.dsl unescape_math.pl \
             $(wildcard manual/*.xml) $(wildcard examples/*.xml) $(wildcard images/*.png)

html-doc:
	rm -rf tmp/ html/
	$(XSLTPROC) -o gappa-preprocessed.xml "$(srcdir)/gappa-preprocess.xsl" "$(srcdir)/gappa.xml"
	$(XSLTPROC) -o html/ "$(srcdir)/gappa.xsl" gappa-preprocessed.xml
	rm gappa-preprocessed.xml
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
	rm -rf tmp/
	$(XSLTPROC) -o gappa-preprocessed.xml "$(srcdir)/gappa-preprocess.xsl" "$(srcdir)/gappa.xml"
	jade -t tex -i tex -d "$(srcdir)/gappa.dsl" /usr/share/xml/declaration/xml.dcl gappa-preprocessed.xml
	rm gappa-preprocessed.xml
	mkdir tmp
	mv gappa-preprocessed.tex tmp/gappa.tex
	"$(srcdir)/unescape_math.pl" tmp/gappa.tex
	sed -e 's/\\Rightarrow/\\rightarrow/g' tmp/gappa.tex > tmp/gappa.tex.2
	mv tmp/gappa.tex.2 tmp/gappa.tex
	(cd tmp ; pdfjadetex gappa.tex ; pdfjadetex gappa.tex ; pdfjadetex gappa.tex ; pdfjadetex gappa.tex) > /dev/null
	mv tmp/gappa.pdf .
	rm -rf tmp/

clean-local:
	rm -rf gappa.pdf html/
