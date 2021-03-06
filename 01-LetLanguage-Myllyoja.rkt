#lang racket
; Requiring eopl is required for define-datatype to function.
(require (lib "eopl.ss" "eopl"))

; This implementation of LET was completed through a combination of
; the Essentials of Programming Languages textbook and the project completed by Dean DeHart:
; https://github.com/Deanout/letlang/blob/master/LetLang.rkt

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
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
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
)

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

; The ultimate payoff; the run function runs a given program by running value-of-program. Copied from page 71 of the textbook.
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

; Value-of-program extracts the expression from the program and gets the value of the expression. Copied from page 71 of the textbook.
(define value-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
      (value-of exp1 (init-env))))))

; The most important function, performs the logic of the program by evaluating expressions passed to it.
(define value-of
  (lambda (exp env)
    (cases expression exp
      (const-exp (num) (num-val num)) ; const-exp returns the corresponding number.
      (var-exp (var) (apply-env env var)) ; var-exp returns the value corresponding to the identifier.
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
            (extend-env var val1 env)))) ; let-exp appends the given variable-value pair to the environment then evaluates the body with that new environment.
    )
  )
)

; The environment, since it isn't part of the language itself, has to be defined manually.
; empty-env is a variable representing an empty environment. This was copied from Lecture 8, slide 3.
(define empty-env
  (lambda ()
    (lambda (search-var)
      (printf "Binding '~s' not found!" search-var)
    )
  )
)

; extend-env adds a variable-value pair to the environment. This was copied from Lecture 8, slide 4.
(define extend-env
  (lambda (saved-var saved-val saved-env)
    (lambda (search-var)
      (if (eqv? search-var saved-var)
        saved-val
        (apply-env saved-env search-var)
      )
    )
  )
)

; apply-env retrieves a value from the environment. This was copied from Lecture 8, slide 5.
(define apply-env
  (lambda (env search-var)
    (env search-var)
  )
)

; init-env is an initial environment, containing arbitrary testing values.
(define init-env
  (lambda ()
    (extend-env
      'i (num-val 1)
        (extend-env
           'v (num-val 5)
             (extend-env
                'x (num-val 10)
                  (empty-env))))))

; Execution and examples.

(DEBUG-print-datatypes)

; Sample Program for testing purposes.
(run "let z = 5
in let x = 3
in let y = -(x,1)
in let x = 4
in -(z, -(x,y))") ; 3