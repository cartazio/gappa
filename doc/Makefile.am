EXTRA_DISTS = gappa examples/*.xml

html-doc:
	#jw -f docbook -b html -l /usr/share/xml/declaration/xml.dcl -o html gappa.xml
	xsltproc -o html/ gappa.xsl gappa.xml

clean-local:
	rm -rf html/
