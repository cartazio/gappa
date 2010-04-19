<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="2.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <xsl:template match="texinline" mode="preprocess">
    <inlineequation><alt role="tex"><xsl:value-of select="."/></alt>
    <graphic fileref="eqn-{generate-id()}.png"/></inlineequation>
  </xsl:template>

  <xsl:template match="texinformal" mode="preprocess">
    <informalequation><alt role="tex"><xsl:value-of select="."/></alt>
    <graphic fileref="eqn-{generate-id()}.png"/></informalequation>
  </xsl:template>

  <xsl:template match="/book" mode="preprocess">
    <xsl:copy>
      <xsl:copy-of select="@*"/>
      <xsl:attribute name="preproc">1</xsl:attribute>
      <xsl:apply-templates mode="preprocess"/>
    </xsl:copy>
  </xsl:template>

  <xsl:template match="@*|node()" mode="preprocess">
    <xsl:copy>
      <xsl:apply-templates select="@*|node()" mode="preprocess"/>
    </xsl:copy>
  </xsl:template>

</xsl:stylesheet>
