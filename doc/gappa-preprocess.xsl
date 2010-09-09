<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <xsl:output method="xml" indent="yes" encoding="UTF-8" media-type="book"
              doctype-public="-//OASIS//DTD DocBook XML V4.3//EN"
              doctype-system="http://www.oasis-open.org/docbook/xml/4.3/docbookx.dtd"/>

  <xsl:template match="texinline">
    <inlineequation><alt role="tex"><xsl:value-of select="."/></alt>
    <graphic fileref="eqn-{generate-id()}.png"/></inlineequation>
  </xsl:template>

  <xsl:template match="texinformal">
    <informalequation><alt role="tex"><xsl:value-of select="."/></alt>
    <graphic fileref="eqn-{generate-id()}.png"/></informalequation>
  </xsl:template>

  <xsl:template match="biblioentry">
    <biblioentry>
      <xsl:choose>
        <xsl:when test="biblioset">
          <xsl:variable name="pubsnumber">
            <xsl:if test="biblioset[@relation='journal']">
              <xsl:value-of select="biblioset/volumenum"/>(<xsl:value-of select="biblioset/issuenum"/>):
            </xsl:if>
            <xsl:value-of select="biblioset/pagenums"/>
          </xsl:variable>
          <xsl:for-each select="biblioset/*">
          <xsl:apply-templates select=".">
            <xsl:with-param name="pubsnumber" select="$pubsnumber"/>
          </xsl:apply-templates>
          </xsl:for-each>
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates/>
        </xsl:otherwise>
      </xsl:choose>
    </biblioentry>
  </xsl:template>

  <xsl:template match="biblioset/pagenums|biblioset/volumenum|biblioset/issuenum"/>

  <xsl:template match="biblioset/title">
    <xsl:param name="pubsnumber"/>
    <xsl:choose>
      <xsl:when test="../@relation='article'">
        <subtitle><xsl:apply-templates/></subtitle>
      </xsl:when>
      <xsl:otherwise>
        <subtitle><emphasis><xsl:apply-templates/></emphasis></subtitle>
        <pubsnumber><xsl:value-of select="$pubsnumber"/></pubsnumber>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="@*|node()">
    <xsl:copy>
      <xsl:apply-templates select="@*|node()"/>
    </xsl:copy>
  </xsl:template>

</xsl:stylesheet>
