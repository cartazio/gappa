<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

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
