<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

  <xsl:include href="gappa-preprocess.xsl"/>

  <xsl:template match="/">
    <xsl:copy>
      <xsl:apply-templates mode="preprocess"/>
    </xsl:copy>
  </xsl:template>

</xsl:stylesheet>
