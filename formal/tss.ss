#lang scheme
(require redex)
    

(define-language λtss
  ; Runtime types and environments
  (RT RTBoolean RTString RTNumber RTFunction)
  (RTEnv ((id (RT ...)) ...))
  
 
  (e v (x RTEnv) (equal? e e RTEnv) (typeof e RTEnv) (let (x e) e) 
     (if e e e RTEnv) (e e RTEnv))
  
  ; Values
  (v number #t #f string (lambda (x) e) + (number +) ++ (string ++))
  
  ; Identifiers
  (x (variable-except lambda let if equal? typeof : int string bool U))
  
  ; Evaluation contexts
  (E (equal? E e RTEnv) (equal? v E RTEnv) (typeof E RTEnv) (let (x E) e)
     (if E e e RTEnv) (E e RTEnv) (v E RTEnv) hole)
  
  )

(define-metafunction λtss
  subst : x v e -> e
  [(subst x_1 v_1 (equal? e_1 e_2 RTEnv))
   (equal? (subst x_1 v_1 e_1) (subst x_1 v_1 e_2) RTEnv)]
  [(subst x_1 v_1 (typeof e_1 RTEnv))
   (typeof (subst x_1 v_1 e_1) RTEnv)]
  [(subst x_1 v_1 (let (x_1 e_1) e_2 RTEnv))
   (let (x_1 (subst x_1 v_1 e_1)) e_2 RTEnv)]
  [(subst x_1 v_1 (let (x_2 e_1) e_2))
   ,(term-let ([x_21 (variable-not-in (term (v_1 e_2)) (term x_2))])
              (term (let (x_21 (subst x_1 v_1 e_1))
                      (subst x_1 v_1 (subst-var x_2 x_21 e_2)))))]
  [(subst x_1 v_1 (if e_1 e_2 e_3 RTEnv))
   (if (subst x_1 v_1 e_1)
       (subst x_1 v_1 e_2)
       (subst x_1 v_1 e_3)
       RTEnv)]
  [(subst x_1 v_1 (e_1 e_2 RTEnv))
   ((subst x_1 v_1 e_1) (subst x_1 v_1 e_2) RTEnv)]
  [(subst x_1 v_1 (lambda (x_1) e_1))
   (lambda (x_1) e_1)]
  [(subst x_1 v_1 (lambda (x_2) e_1)) ; capture avoiding substitution
   ,(term-let ([x_21 (variable-not-in (term (v_1 e_1)) (term x_2))])
              (term (lambda (x_21) (subst x_1 v_1 (subst-var x_2 x_21 e_1)))))]
  
  [(subst x_1 v_1 v_2) v_2]
  [(subst x_1 v_1 (x_1 RTEnv)) v_1]
  [(subst x_1 v_1 (x_2 RTEnv)) (x_2 RTEnv)])
    

(define-metafunction λtss
  subst-var : x x any -> e
  [(subst-var x_1 x_2 x_1) x_2]
  [(subst-var x_1 x_2 (any_1 ...)) ((subst-var x_1 x_2 any_1) ...)]
  [(subst-var x_1 x_2 any_1) any_1])

(define red
  (reduction-relation 
   λtss
   (--> (in-hole E  (equal? v_1 v_2 RTEnv))
        (in-hole E ,(equal? (term v_1) (term v_2))))
   (--> (in-hole E (typeof number_1 RTEnv))
        (in-hole E "number"))
   (--> (in-hole E (typeof string_1 RTEnv))
        (in-hole E "string"))
   (--> (in-hole E (typeof #t RTEnv))
        (in-hole E "boolean"))
   (--> (in-hole E (typeof #f RTEnv))
        (in-hole E "boolean"))
   (--> (in-hole E (typeof (lambda (x_1) e_1) RTEnv))
        (in-hole E "function"))
   (--> (in-hole E (if #t e_1 e_2 RTEnv))
        (in-hole E e_1))
   (--> (in-hole E (if #f e_1 e_2 RTEnv))
        (in-hole E e_2))
   (--> (in-hole E (let (x_1 v_1) e_1))
        (in-hole E (subst x_1 v_1 e_1))
        "let")
   (--> (in-hole E (+ number_1 RTEnv))
        (in-hole E (number_1 +)))
   (--> (in-hole E (++ string_1 RTEnv))
        (in-hole E (string_1 ++)))
   (--> (in-hole E ((string_1 ++) string_2 RTEnv))
        (in-hole E ,(string-append (term string_1) (term string_2))))
   (--> (in-hole E ((number_1 +) number_2 RTEnv))
        (in-hole E ,(+ (term number_1) (term number_2))))
   (--> (in-hole E ((lambda (x_1) e_1) v_1 RTEnv))
        (in-hole E (subst x_1 v_1 e_1)))))


(define e0 (term ((+ 1 ()) 2 ())))

(test-->> red e0 3)

(define e1 (term (equal? ((+ 1 ()) 10 ()) 11 ())))
(test-->> red e1 #t)

(define e2 (term (if (equal? 1 1 ()) 2424 83 ())))
(test-->> red e2 2424)

(test-->> red
          (term (let [x 10] (x ())))
          10)

(define e3 (term (let [x ,e0] ((+ (x ()) ()) 90 ()))))
(test-->> red e3 93)

(test-->>
 red
 (term (let [f (lambda (x) (x ()))]
         ((f ()) 10 ())))
 10)

(test-->>
 red
 (term (typeof "hello" ()))
 "string")

(test-->>
 red
 (term (if #t "hello" "goodbye" ()))
 "hello")

(define generic-add
  (term (lambda (x)
          (if (equal? (typeof (x ()) ()) "number" ())
              ((+ (x ()) ()) 1 ())
              (if (equal? (typeof (x ()) ()) "string" ())
                  ((++ (x ()) ()) "hello" ())
                  (x ())
                  ())
              ()))))

(test-->>
 red
 (term (let (generic-add ,generic-add)
          ((generic-add ()) "hello" ())))
 "hellohello")

(test-results)
