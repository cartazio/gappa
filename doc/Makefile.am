EXTRA_DISTS = gappa.xml gappa-preprocess.xsl gappa.xsl manual/*.xml examples/*.xml

html-doc:
	xsltproc -o gappa-preprocessed.xml gappa-preprocess.xsl gappa.xml
	xsltproc -o html/ gappa.xsl gappa-preprocessed.xml
	rm gappa-preprocessed.xml
	mkdir html/tmp
	cd html/tmp ; \
	mv ../tex-math-equations.tex . ; \
	latex tex-math-equations.tex ; \
	~/src/dvi2bitmap-0.13b3/dvi2bitmap --magnification=4 --scaledown=4 tex-math-equations.dvi ; \
	mv *.png ..
	rm -r html/tmp

clean-local:
	rm -rf html/
