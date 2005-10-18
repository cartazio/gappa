<!DOCTYPE style-sheet PUBLIC "-//James Clark//DTD DSSSL Style Sheet//EN"
[
  <!ENTITY print-ss SYSTEM "/usr/share/sgml/docbook/stylesheet/dsssl/modular/print/docbook.dsl" CDATA dsssl>
]>

<style-sheet>
<style-specification id="tex" use="print-stylesheet">
<style-specification-body> 

(define tex-backend #t)

(define %hyphenation% #t)
(define %default-quadding% 'justify)
(define %language% 'EN)
(define %paper-type% "A4")
(define %section-autolabel% #t)
(define %mono-font-family% "Computer Modern Typewriter")
(define %verbatim-size-factor% #f)
(define %block-start-indent% 2em)

(element (inlineequation graphic) (empty-sosofo))
(element (informalequation graphic) (empty-sosofo))
(element (inlineequation alt)
  (make sequence (literal "BEGINTEXLITERAL") (literal "$")
    (literal (data (current-node))) (literal "$") (literal "ENDTEXLITERAL")))
(element (informalequation alt)
  (make paragraph quadding: 'center
    (make sequence (literal "BEGINTEXLITERAL") (literal "$\\displaystyle ")
      (literal (data (current-node))) (literal "$") (literal "ENDTEXLITERAL"))))
(element code ($mono-seq$))

</style-specification-body>
</style-specification>
<external-specification id="print-stylesheet" document="print-ss">
</style-sheet>
