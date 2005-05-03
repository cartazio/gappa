<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
                                                                        
       
  <!-- import the real stylesheet -->
  <xsl:import href="file:///usr/share/xml/docbook/stylesheet/nwalsh/xhtml/chunk.xsl"/>
                                                                        
       
  <!-- make HTML 4.01 output with utf-8 encoding -->
  <xsl:output method="html" encoding="utf-8"
    doctype-public="-//W3C//DTD HTML 4.01 Transitional//EN"
    doctype-system="http://www.w3.org/TR/html4/loose.dtd" indent="no"/>
                                                                        
       
  <!-- custom tables -->
  <xsl:variable name="html.cellpadding">0</xsl:variable>
  <xsl:variable name="html.cellspacing">0</xsl:variable>
                                                                        
       
  <!-- no link targets -->
  <xsl:variable name="ulink.target"/>
                                                                        
       
  <!-- shade verbatim stuff -->
  <xsl:param name="shade.verbatim">1</xsl:param>
  <xsl:attribute-set name="shade.verbatim.style">
    <xsl:attribute name="border">0</xsl:attribute>
    <xsl:attribute name="bgcolor">#EEEEEE</xsl:attribute>
  </xsl:attribute-set>
                                                                        
       
</xsl:stylesheet>

