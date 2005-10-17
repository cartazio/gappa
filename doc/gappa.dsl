<!DOCTYPE style-sheet PUBLIC "-//James Clark//DTD DSSSL Style Sheet//EN"
[
  <!ENTITY print-ss SYSTEM "/usr/share/sgml/docbook/stylesheet/dsssl/modular/print/docbook.dsl" CDATA dsssl>
]>

<style-sheet>
<style-specification id="tex" use="print-stylesheet">
<style-specification-body> 

(define %hyphenation% #t)
(define %default-quadding% 'justify)
(define %language% 'EN)
(define %paper-type% "A4")
(define %section-autolabel% #t)

(element (inlineequation graphic) (empty-sosofo))
(element (informalequation graphic) (empty-sosofo))
(element (inlineequation alt)
  (make sequence (literal "BEGINTEXLITERAL") (literal "$")
    (literal (data (current-node))) (literal "$") (literal "ENDTEXLITERAL")))
(element (informalequation alt)
  (make sequence (literal "BEGINTEXLITERAL") (literal "$$")
    (literal (data (current-node))) (literal "$$") (literal "ENDTEXLITERAL")))
(element code ($mono-seq$))

(define (generic-list-item indent-step line-field)
  (let* ((itemcontent (children (current-node)))
         (first-child (node-list-first itemcontent))
         (spacing (inherited-attribute-string (normalize "spacing"))))
    (make display-group
      start-indent: (+ (inherited-start-indent) indent-step)
      (make paragraph
        use: (cond
              ((equal? (gi first-child) (normalize "programlisting"))
               verbatim-style)
              ((equal? (gi first-child) (normalize "screen"))
               verbatim-style)
              ((equal? (gi first-child) (normalize "synopsis"))
               verbatim-style)
              ((equal? (gi first-child) (normalize "literallayout"))
               linespecific-style)
              ((equal? (gi first-child) (normalize "address"))
               linespecific-style)
              (else
               nop-style))
        space-before: (if (equal? (normalize "compact") spacing)
                          0pt
                          %para-sep%)
        first-line-start-indent: (- indent-step)
        (make sequence
          line-field)
	(with-mode listitem-content-mode
	  (process-node-list first-child))
        (process-node-list (node-list-rest itemcontent))))))

</style-specification-body>
</style-specification>
<external-specification id="print-stylesheet" document="print-ss">
</style-sheet>
