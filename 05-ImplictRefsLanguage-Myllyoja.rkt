#lang racket
; Requiring eopl is required for define-datatype to function.
(require (lib "eopl.ss" "eopl"))

; This implementation of EXPLICIT-REFS was completed through a combination of
; the Essentials of Programming Languages textbook and the previous EXPLICIT-REFS language,
; which was completed in part with code from Dean DeHart:
; https://github.com/Deanout/letlang/blob/master/LetLang.rkt
; Code from Chenyu Kang was also used:
; https://github.com/chenyukang/eopl/blob/master/ch4/base/explicit-lang.scm

; SSLGEN is a Scheme package which, given a simple lexical and grammatical specification, will create a scanner and a parser for a language, creating datatype definitions for you.
; Thus, manually writing most of the (define-datatype lines is not required. All that is then needed is to create the implementation for the language.

; Lexical specification. This was copied from Appendix B, page 383 of the textbook.
; This list defines a number of three-item sets, one for each of the language's tokens.
;   The first value is a human readable name for the token,
;   the second defines a matching pattern.
(define lexical-spec
  '((white-sp (whitespace) skip) ; If the scanner finds whitespace, skip this symbol.
    (comment ("%" (arbno (not #\newline))) skip) ; If the scanner finds a % sign, skip an arbitrary number of symbol proceeding it until the next newline character
    (identifier (letter (arbno (or letter digit))) symbol) ; If the scanner finds a letter, followed by an arbitrary number of letters or digits, define it as a language symbol.
    (number (digit (arbno digit)) number) ; If the scanenr finds a number, define it as a value.
    (number ("-" digit (arbno digit)) number) ; allow for negative numbers
  )
)

; Grammatical specification. This is a list of definitions, each definition having three parts.
; The first part is the non-terminal being defined, the second part is the definition of that non-terminal (in parenthesis),
; and the third part is the variation name.
; This was modified from code from Appendix B, page 412 of the textbook, as well as content from pages 60 and 69 of the textbook.
(define grammatical-spec
  '((program    (expression) a-program)
    (expression (number)     const-exp)
    (expression (identifier) var-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" expression) zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("(" expression expression ")") call-exp)
    (expression ("proc" "(" identifier ")" expression) proc-exp)
    (expression ("letrec" identifier "(" identifier ")" "=" expression "in" expression) letrec-exp)
    ; New grammar for EXPLICIT-REF.
    (expression ("begin" expression (arbno ";" expression) "end") begin-exp)
    (expression ("set" identifier "=" expression) assign-exp)
    ;(expression ("newref" "(" expression ")") newref-exp)
    ;(expression ("deref" "(" expression ")") deref-exp)
    ;(expression ("setref" "(" expression "," expression ")") setref-exp)
  )
)
; Provided grammar:
; Lc-exp ::= Identifier
;   var-exp (var)
;        ::= (lambda ({Identifier}∗) Lc-exp)
;   lambda-exp (bound-vars body)
;        ::=(Lc-exp {Lc-exp}∗)
;   app-exp (rator rands)

; The below SSLGEN-specific code was adapted from Dean DeHart's answer.
; SSLGEN, do the thing! This defines the data types for program and expression.
(sllgen:make-define-datatypes lexical-spec grammatical-spec)
; This defines the scan&parse function used to convert a string of characters into an abstract syntax tree!
(define scan&parse
  (sllgen:make-string-parser lexical-spec grammatical-spec))
; This debug function prints the list of datatypes, given the lexical and grammatical specification.
;   You can't just include the line on its own for some reason.
(define DEBUG-print-datatypes
  (lambda () (sllgen:list-define-datatypes lexical-spec grammatical-spec)))
; Create a console that reads, evaluates, and prints whatever code you provide it in a loop!
;(define DEBUG-console
;  (sllgen:make-rep-loop "let> "
;  (lambda (pgm) (value-of-program pgm))
;  (sllgen:make-stream-parser the-lexical-spec the-grammar)))

; Now for the meat of the language, the interpreter!

; Define the data type for expression values. This was copied from page 70 of the textbook.
(define-datatype expval expval? ; expval has two variations.
  (num-val
    (num number?)) ; the num-val variation must be a number.
  (bool-val
    (bool boolean?)) ; the bool-val varation must be a boolean.
  (proc-val
    (proc proc?)) ; the proc-val variation must be a procedure.
  (ref-val
    (ref reference?)) ; the ref-val variation must be a reference.
)

; Define the procedure data type used in expval.
(define proc?
  (lambda (val)
    (procedure? val)))

(define procedure
  (lambda (var body env)
    (lambda (val)
      (value-of body (extend-env var val env)))))

(define apply-procedure
  (lambda (proc1 val)
    (proc1 (newref val))))


; Define the observers for the expval data type. These were copied from page 70 of the textbook.
(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (printf "Could not extract numeric value from ~s" val)))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (printf "Could not extract boolean value from ~s" val)))))

(define expval->proc
  (lambda (val)
    (cases expval val
      (proc-val (proc) proc)
      (else (printf "Could not extract procedure value from ~s" val)))))

(define expval->ref
  (lambda (val)
    (cases expval val
      (ref-val (ref) ref)
      (else (printf "Could not extract reference value from ~s" val)))))

; The ultimate payoff; the run function runs a given program by running value-of-program. Copied from page 71 of the textbook.
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

; Value-of-program extracts the expression from the program and gets the value of the expression. Copied from page 71 of the textbook.
(define value-of-program
  (lambda (pgm)
    (initialize-store!)
    (cases program pgm
      (a-program (exp1)
      (value-of exp1 (init-env))))))

; The most important function, performs the logic of the program by evaluating expressions passed to it.
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num)) ; const-exp returns the corresponding number.
      (var-exp (var) (deref (apply-env env var))) ; var-exp returns the value corresponding to the identifier.
      (proc-exp (var body) (proc-val (procedure var body env))) ; proc-exp returns the value corresponding to the procedure.
      (diff-exp (exp1 exp2)
        (let ([val1 (value-of exp1 env)]
              [val2 (value-of exp2 env)])
          (let ([num1 (expval->num val1)]
                [num2 (expval->num val2)])
            (num-val (- num1 num2))))) ; diff-exp returns the difference between two numbers.
      (zero?-exp (exp1)
        (let ((val1 (value-of exp1 env)))
          (let ((num1 (expval->num val1)))
            (if (zero? num1)
              (bool-val #t)
              (bool-val #f))))) ; zero-exp returns a bool-val depending on if the provided expression evaluates to zero.
      (if-exp (exp1 exp2 exp3)
        (let ((val1 (value-of exp1 env)))
          (if (expval->bool val1)
            (value-of exp2 env)
            (value-of exp3 env)))) ; if-exp returns the value of one of two expressions depending on the value of another expression.
      (let-exp (var exp1 body)
        (let ((val1 (value-of exp1 env)))
          (value-of body
            (extend-env var (newref val1) env)))) ; let-exp appends the given variable-value pair to the environment then evaluates the body with that new environment.
      (call-exp (rator rand)
        (let ((proc (expval->proc (value-of rator env))) (arg (value-of rand env)))
           (apply-procedure proc arg)
        )
      )
      (letrec-exp (proc-name proc-var proc-body letrec-body)
        (value-of letrec-body (extend-env-rec proc-name proc-var proc-body env))
      )
      ; Explicit ref expressions defined on line 113.
      (begin-exp (exp1 exps)
        (letrec
          ((value-of-begins
            (lambda (e1 es)
              (let ((v1 (value-of e1 env)))
                (if (null? es)
                  v1
                  (value-of-begins (car es) (cdr es)))))))
        (value-of-begins exp1 exps)))
      (assign-exp (var exp1)
        (begin
          (setref! (apply-env env var) (value-of exp1 env))
          (num-val 27))) ;return a dummy value.
    )
  )
)

; The store. Taken from page 111 and 112 of the textbook.
(define the-store 'uninitialized)

(define empty-store
  (lambda () '()))

(define get-store
  (lambda () the-store))

(define initialize-store!
  (lambda ()
    (set! the-store (empty-store))))

(define reference?
  (lambda (v)
    (integer? v)))

(define newref
  (lambda (val)
    (let ((next-ref (length the-store)))
      (set! the-store (append the-store (list val)))
      next-ref)))

(define deref
  (lambda (ref)
    (list-ref the-store ref)))

(define setref!
  (lambda (ref val)
    (set! the-store
      (letrec
        ((setref-inner
          (lambda (store1 ref1)
            (cond
              ((null? store1)
                (printf "Could not extract reference value from ~s" ref))
              ((zero? ref1)
                (cons val (cdr store1)))
              (else
                (cons
                  (car store1)
                  (setref-inner
                    (cdr store1) (- ref1 1))))))))
        (setref-inner the-store ref)))))

; The environment, since it isn't part of the language itself, has to be defined manually.
; New environment from page 86 of the textbook.
(define-datatype environment environment?
  (empty-env)
  (extend-env
    (var symbol?)
    (val reference?) ; expval is replaced with reference in IMPLICIT-REF
    (env environment?))
  (extend-env-rec
    (p-name symbol?)
    (b-var symbol?)
    (body expression?)
    (env environment?)))

(define apply-env
  (lambda (env search-var)
    (cases environment env
      (empty-env ()
        (printf "Binding '~s' not found!" search-var))
      (extend-env (saved-var saved-val saved-env)
        (if (eqv? saved-var search-var)
          saved-val
          (apply-env saved-env search-var))
        )
      (extend-env-rec (p-name b-var p-body saved-env)
        (if (eqv? search-var p-name)
          (newref (proc-val (procedure b-var p-body env))) ; Build the proc-val at apply time. Now wrapped in newref.
          (apply-env saved-env search-var))
        )
    )
  )
)

; The location function returns the location of a given symbols in a list of symbols, or false if the value is not present.
(define location
  (lambda (sym syms)
    (cond
     ((null? syms) #f)
     ((eqv? sym (car syms)) 0)
     ((location sym (cdr syms))
      => (lambda (n)
           (+ n 1)))
(else #f))))

; init-env is an initial environment, containing arbitrary testing values.
(define init-env
  (lambda ()
    (empty-env)))

; Execution and examples.

(DEBUG-print-datatypes)

; Sample Program for testing purposes.
(run "let f = proc (x) proc (y)
begin
set x = -(x,-1);
-(x,y)
end
in ((f 44) 33)") ; 12