EXTRA_DISTS = gappa.xml gappa.xsl manual/*.xml examples/*.xml

html-doc:
	xsltproc -o html/ gappa.xsl gappa.xml
	mkdir -p html/tmp
	cd html/tmp ; \
	mv ../tex-math-equations.tex . ; \
	latex tex-math-equations.tex ; \
	~/src/dvi2bitmap-0.13b3/dvi2bitmap --magnification=4 --scaledown=4 tex-math-equations.dvi ; \
	mv *.png ..
	rm -r html/tmp

clean-local:
	rm -rf html/
