#lang racket
; Requiring eopl is required for define-datatype to function.
(require (lib "eopl.ss" "eopl"))

; This implementation of CHECKED was completed through a combination of
; the Essentials of Programming Languages textbook and the previous LETREC language,
; which was completed in part with code from Dean DeHart:
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
    (expression ("zero?" expression) zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("(" expression expression ")") call-exp)
    ; Added types to the proc and letrec expressions.
    (expression ("proc" "(" identifier ":" type ")" expression) proc-exp)
    (expression ("letrec" type identifier "(" identifier ":" type ")" "=" expression "in" expression) letrec-exp)
    ; Types are added to the grammar.
    (type       ("int") int-type)
    (type       ("bool") bool-type)
    (type       ("(" type "->" type ")") proc-type)
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
)

; Typechecking code from page 242.
(define check-equal-type!
  (lambda (ty1 ty2 exp)
    (if (not (equal? ty1 ty2))
      (report-unequal-types ty1 ty2 exp)
      42)))

(define report-unequal-types
  (lambda (ty1 ty2 exp)
    (eopl:error 'check-equal-type!
      "Types didn’t match: ~s != ~a in~%~a"
      (type-to-external-form ty1)
      (type-to-external-form ty2)
      exp)))

(define type-to-external-form
  (lambda (ty)
    (cases type ty
      (int-type () 'int)
      (bool-type () 'bool)
      (proc-type (arg-type result-type)
        (list
          (type-to-external-form arg-type)
          '->
          (type-to-external-form result-type))))))

(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1) (type-of exp1 (init-tenv))))))

(define type-of
  (lambda (exp tenv)
    (cases expression exp
      (const-exp (num) (int-type))
      (var-exp (var) (apply-tenv tenv var))
      (diff-exp (exp1 exp2)
        (let ((ty1 (type-of exp1 tenv))
              (ty2 (type-of exp2 tenv)))
          (check-equal-type! ty1 (int-type) exp1)
          (check-equal-type! ty2 (int-type) exp2)
          (int-type)))
      (zero?-exp (exp1)
        (let ((ty1 (type-of exp1 tenv)))
          (check-equal-type! ty1 (int-type) exp1)
          (bool-type)))
      (if-exp (exp1 exp2 exp3)
        (let ((ty1 (type-of exp1 tenv))
              (ty2 (type-of exp2 tenv))
              (ty3 (type-of exp3 tenv)))
          (check-equal-type! ty1 (bool-type) exp1)
          (check-equal-type! ty2 ty3 exp)
          ty2))
      (let-exp (var exp1 body)
        (let ((exp1-type (type-of exp1 tenv)))
          (type-of body
            (extend-tenv var exp1-type tenv))))
      (proc-exp (var var-type body)
        (let ((result-type
          (type-of body
            (extend-tenv var var-type tenv))))
          (proc-type var-type result-type)))
      (call-exp (rator rand)
        (let ((rator-type (type-of rator tenv))
              (rand-type  (type-of rand tenv)))
          (cases type rator-type
            (proc-type (arg-type result-type)
              (begin
                (check-equal-type! arg-type rand-type rand)
                result-type))
              (else
                (printf "Expression ~s (~s) does not have an operator type." rator-type rator)))))
      (letrec-exp (p-result-type p-name b-var b-var-type
                   p-body letrec-body)
        (let ((tenv-for-letrec-body
              (extend-tenv p-name
              (proc-type b-var-type p-result-type)
               tenv)))
          (let ((p-body-type
                  (type-of p-body
                    (extend-tenv b-var b-var-type
                      tenv-for-letrec-body))))
            (check-equal-type!
              p-body-type p-result-type p-body)
            (type-of letrec-body tenv-for-letrec-body)))))))
      
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
    (proc1 val)))


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
      (proc-exp (var type body) (proc-val (procedure var body env))) ; proc-exp returns the value corresponding to the procedure.
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
      (call-exp (rator rand)
        (let ((proc (expval->proc (value-of rator env))) (arg (value-of rand env)))
           (apply-procedure proc arg)
        )
      )
      (letrec-exp (type1 proc-name proc-var type2 proc-body letrec-body)
        (value-of letrec-body (extend-env-rec proc-name proc-var proc-body env))
      )
    )
  )
)

; The environment, since it isn't part of the language itself, has to be defined manually.
; New environment from page 86 of the textbook.
(define-datatype environment environment?
  (empty-env)
  (extend-env
    (var symbol?)
    (val expval?)
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
          (proc-val (procedure b-var p-body env)) ; Build the proc-val at apply time.
          (apply-env saved-env search-var))
        )
    )
  )
)

; init-env is an initial environment, containing arbitrary testing values.
(define init-env
  (lambda ()
    (empty-env)))

; Type environment. Copied from https://github.com/chenyukang/eopl/blob/master/ch7/base/checked.scm
(define-datatype type-environment type-environment?
  (empty-tenv-record)
  (extended-tenv-record
   (sym symbol?)
   (type type?)
   (tenv type-environment?)))

(define empty-tenv empty-tenv-record)
(define extend-tenv extended-tenv-record)

(define apply-tenv
  (lambda (tenv sym)
    (cases type-environment tenv
      (empty-tenv-record ()
        (error 'apply-tenv "Unbound variable ~s" sym))
      (extended-tenv-record (sym1 val1 old-env)
        (if (eqv? sym sym1)
          val1
          (apply-tenv old-env sym))))))

(define init-tenv
  (lambda ()
    (extend-tenv 'x (int-type)
      (extend-tenv 'v (int-type)
        (extend-tenv 'i (int-type)
          (empty-tenv))))))


; Execution and examples.

(DEBUG-print-datatypes)

; Sample Program for testing purposes.
(run "letrec int double (n : int) = if zero? n then 0 else -((double -(n,1)), -2)
in (double 3)") ; 6