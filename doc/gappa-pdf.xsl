<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="2.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:exslt="http://exslt.org/common">

  <xsl:output method="xml" indent="yes" encoding="ISO-8859-15" media-type="book"
              doctype-public="-//OASIS//DTD DocBook XML V4.3//EN"
              doctype-system="http://www.oasis-open.org/docbook/xml/4.3/docbookx.dtd"/>

  <xsl:include href="gappa-preprocess.xsl"/>

  <xsl:template match="/" priority="10">
    <xsl:copy-of select="exslt:node-set($preprocessed)"/>
  </xsl:template>

</xsl:stylesheet>
