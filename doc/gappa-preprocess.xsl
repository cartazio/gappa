<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <xsl:output method="xml" indent="yes" encoding="ISO-8859-15" media-type="book"
              doctype-public="-//OASIS//DTD DocBook XML V4.3//EN"
              doctype-system="file:///usr/share/xml/docbook/schema/dtd/4.3/docbookx.dtd"/>

  <xsl:template match="texinline">
    <inlineequation><alt role="tex"><xsl:value-of select="."/></alt>
    <graphic fileref="eqn-{generate-id()}.png"/></inlineequation>
  </xsl:template>

  <xsl:template match="texinformal">
    <informalequation><alt role="tex"><xsl:value-of select="."/></alt>
    <graphic fileref="eqn-{generate-id()}.png"/></informalequation>
  </xsl:template>

  <xsl:template match="@*|node()">
    <xsl:copy>
      <xsl:apply-templates select="@*|node()"/>
    </xsl:copy>
  </xsl:template>

</xsl:stylesheet>
