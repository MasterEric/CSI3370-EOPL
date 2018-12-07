#lang racket
; Requiring eopl is required for define-datatype to function.
(require (lib "eopl.ss" "eopl"))

; This implementation of INFERRED was completed through a combination of
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
    ; Added types to the proc expressions.
    (expression ("proc" "(" identifier ":" optional-type ")" expression) proc-exp)
    (expression ("letrec" optional-type identifier "(" identifier ":" optional-type ")" "=" expression "in" expression) letrec-exp)
    ; Types are added to the grammar.
    (type       ("int") int-type)
    (type       ("bool") bool-type)
    (type       ("(" type "->" type ")") proc-type)
    ; If a type is made optional, it is to be inferred by how the function is used.
    (optional-type ("?") no-type) 
    (optional-type (type) a-type)
    ; This additional type is used during substitiution.
    (type ("%tvar-type" number) tvar-type)
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
          (type-to-external-form result-type)))
      (tvar-type (serial-number)
        (string->symbol
          (string-append
            "ty"
            (number->string serial-number)))))))

(define type-of
  (lambda (exp tenv subst)
    (cases expression exp
      (const-exp (num) (an-answer (int-type) subst))
      (diff-exp (exp1 exp2)
        (cases answer (type-of exp1 tenv subst)
          (an-answer (ty1 subst1)
            (let ((subst1
                    (unifier ty1 (int-type) subst1 exp1)))
              (cases answer (type-of exp2 tenv subst1)
                (an-answer (ty2 subst2)
                  (let ((subst2
                          (unifier ty2 (int-type)
                            subst2 exp2)))
                    (an-answer (int-type) subst2))))))))
      (zero?-exp (exp1)
        (cases answer (type-of exp1 tenv subst)
          (an-answer (ty1 subst1)
            (let ((subst2
                    (unifier ty1 (int-type) subst1 exp)))
              (an-answer (bool-type) subst2)))))
      (if-exp (exp1 exp2 exp3)
        (cases answer (type-of exp1 tenv subst)
          (an-answer (ty1 subst)
            (let ((subst
                    (unifier ty1 (bool-type) subst exp1)))
              (cases answer (type-of exp2 tenv subst)
                (an-answer (ty2 subst)
                  (cases answer (type-of exp3 tenv subst)
                    (an-answer (ty3 subst)
                      (let ((subst
                              (unifier ty2 ty3 subst exp)))
                        (an-answer ty2 subst))))))))))
      (var-exp (var)
        (an-answer (apply-tenv tenv var) subst))
      (let-exp (var exp1 body)
        (cases answer (type-of exp1 tenv subst)
          (an-answer (exp1-type subst)
            (type-of body
              (extend-tenv var exp1-type tenv)
              subst))))
      (proc-exp (var otype body)
        (let ((var-type (otype->type otype)))
          (cases answer (type-of body
                          (extend-tenv var var-type tenv)
                          subst)
            (an-answer (body-type subst)
              (an-answer
                (proc-type var-type body-type)
                subst)))))
      (call-exp (rator rand)
        (let ((result-type (fresh-tvar-type)))
          (cases answer (type-of rator tenv subst)
            (an-answer (rator-type subst)
              (cases answer (type-of rand tenv subst)
                (an-answer (rand-type subst)
                  (let ((subst
                          (unifier
                            rator-type
                            (proc-type
                              rand-type result-type)
                            subst
                            exp)))
                    (an-answer result-type subst))))))))
      (letrec-exp (p-result-otype p-name b-var b-var-otype
                   p-body letrec-body)
        (let ((p-result-type (otype->type p-result-otype))
              (p-var-type (otype->type b-var-otype)))
          (let ((tenv-for-letrec-body
                  (extend-tenv p-name
                    (proc-type p-var-type p-result-type)
                    tenv)))
            (cases answer (type-of p-body
                            (extend-tenv b-var p-var-type
                              tenv-for-letrec-body)
                            subst)
              (an-answer (p-body-type subst)
                (let ((subst
                        (unifier p-body-type p-result-type
                          subst p-body)))
                  (type-of letrec-body
                    tenv-for-letrec-body
                    subst)))))))
    )
  )
)

(define tvar-type?
  (lambda (ty)
    (cases type ty
           (tvar-type (serial-number) #t)
(else #f))))

(define proc-type->arg-type
  (lambda (ty)
    (cases type ty
           (proc-type (arg-type result-type) arg-type)
           (else (error 'proc-type->arg-type
                             "Not a proc type: ~s" ty)))))

(define proc-type->result-type
  (lambda (ty)
    (cases type ty
           (proc-type (arg-type result-type) result-type)
           (else (error 'proc-type->result-types
"Not a proc type: ~s" ty)))))

(define proc-type?
  (lambda (ty)
    (cases type ty
           (proc-type (t1 t2) #t)
(else #f))))

(define equal-up-to-gensyms?
  (lambda (sexp1 sexp2)
    (equal?
      (apply-subst-to-sexp (canonical-subst sexp1) sexp1)
      (apply-subst-to-sexp (canonical-subst sexp2) sexp2))))

(define canonical-subst
  (lambda (sexp)
    (let loop ((sexp sexp) (table '()))
      (cond
        ((null? sexp) table)
        ((tvar-type-sym? sexp)
          (cond
            ((assq sexp table) table)
            (else
              (cons
                (cons sexp (ctr->ty (length table)))
                table))))
        ((pair? sexp)
          (loop (cdr sexp)
            (loop (car sexp) table)))
        (else table)))))

(define tvar-type-sym?
(lambda (sym)
(and (symbol? sym)
(char-numeric? (car (reverse (symbol->list sym)))))))

(define symbol->list
(lambda (x)
(string->list (symbol->string x))))

(define apply-subst-to-sexp
(lambda (subst sexp)
(cond
((null? sexp) sexp)
((tvar-type-sym? sexp)
(cdr (assq sexp subst)))
((pair? sexp)
(cons
(apply-subst-to-sexp subst (car sexp))
(apply-subst-to-sexp subst (cdr sexp))))
(else sexp))))

(define ctr->ty
(lambda (n)
(string->symbol
(string-append "tvar" (number->string n)))))

; Implicit type checking.
(define apply-one-subst
  (lambda (ty0 tvar ty1)
    (cases type ty0
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (arg-type result-type)
        (proc-type
          (apply-one-subst arg-type tvar ty1)
          (apply-one-subst result-type tvar ty1)))
      (tvar-type (sn)
        (if (equal? ty0 tvar) ty1 ty0)))))

(define apply-subst-to-type
  (lambda (ty subst)
    (cases type ty
      (int-type () (int-type))
      (bool-type () (bool-type))
      (proc-type (t1 t2)
        (proc-type
          (apply-subst-to-type t1 subst)
          (apply-subst-to-type t2 subst)))
      (tvar-type (sn)
        (let ((tmp (assoc ty subst)))
          (if tmp
            (cdr tmp)
            ty))))))

(define empty-subst (lambda () '()))

(define extend-subst
  (lambda (subst tvar ty)
    (cons
      (cons tvar ty)
      (map
        (lambda (p)
          (let ((oldlhs (car p))
                (oldrhs (cdr p)))
            (cons
              oldlhs
              (apply-one-subst oldrhs tvar ty))))
        subst))))

(define unifier
  (lambda (ty1 ty2 subst exp)
    (let ((ty1 (apply-subst-to-type ty1 subst))
          (ty2 (apply-subst-to-type ty2 subst)))
      (cond
        ((equal? ty1 ty2) subst)
        ((tvar-type? ty1)
         (if (no-occurrence? ty1 ty2)
           (extend-subst subst ty1 ty2)
           (printf "No occurrence violation (~s, ~s, ~s)" ty1 ty2 exp)))
        ((tvar-type? ty2)
         (if (no-occurrence? ty2 ty1)
           (extend-subst subst ty2 ty1)
           (printf "No occurrence violation (~s, ~s, ~s)" ty2 ty1 exp)))
        ((and (proc-type? ty1) (proc-type? ty2))
         (let ((subst (unifier
                        (proc-type->arg-type ty1)
                        (proc-type->arg-type ty2)
                        subst exp)))
         (let ((subst (unifier
                        (proc-type->result-type ty1)
                        (proc-type->result-type ty2)
                        subst exp)))
           subst)))
        (else (printf "Unification failure (~s, ~s, ~s)" ty1 ty2 exp))))))

(define no-occurrence?
  (lambda (tvar ty)
    (cases type ty
      (int-type () #t)
      (bool-type () #t)
      (proc-type (arg-type result-type)
        (and
          (no-occurrence? tvar arg-type)
          (no-occurrence? tvar result-type)))
      (tvar-type (serial-number) (not (equal? tvar ty))))))

(define otype->type
  (lambda (otype)
    (cases optional-type otype
      (no-type () (fresh-tvar-type))
      (a-type (ty) ty))))

(define fresh-tvar-type
  (let ((sn 0))
    (lambda ()
      (set! sn (+ sn 1))
      (tvar-type sn))))

(define pair-of
    (lambda (pred1 pred2)
      (lambda (val)
(and (pair? val) (pred1 (car val)) (pred2 (cdr val))))))

(define substitution?
(list-of (pair-of tvar-type? type?)))

(define-datatype answer answer?
  (an-answer
    (ty type?)
    (subst substitution?)))

(define type-of-program
  (lambda (pgm)
    (cases program pgm
      (a-program (exp1)
        (cases answer (type-of exp1
                        (init-tenv) (empty-subst))
          (an-answer (ty subst)
            (apply-subst-to-type ty subst)))))))

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
(run "letrec
? foo (x : ?) = if zero? x
then 1
else -(x, (foo -(x,1)))
in (foo 8)") ; 5