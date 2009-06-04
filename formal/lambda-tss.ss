#lang scheme
(require redex)

(define-language λtss
  (e v x (equal? e e) (typeof e) (let (x e) e) (if e e e) (e e))
  (v number #t #f string (lambda (x) e) + (number +) ++ (string ++))
  (x (variable-except lambda let if equal? typeof))
  (E (equal? E e) (equal? v E) (typeof E) (let (x E) e) (if E e e) (E e) (v E) hole))


    
(define-metafunction λtss
  subst : x v e -> e
  [(subst x_1 v_1 (equal? e_1 e_2))
   (equal? (subst x_1 v_1 e_1) (subst x_1 v_1 e_2))]
  [(subst x_1 v_1 (typeof e_1))
   (typeof (subst x_1 v_1 e_1))]
  [(subst x_1 v_1 (let (x_1 e_1) e_2))
   (let (x_1 (subst x_1 v_1 e_1)) e_2)]
  [(subst x_1 v_1 (let (x_2 e_1) e_2))
   ,(term-let ([x_21 (variable-not-in (term (v_1 e_2)) (term x_2))])
              (term (let (x_21 (subst x_1 v_1 e_1))
                      (subst x_1 v_1 (subst-var x_2 x_21 e_2)))))]
  [(subst x_1 v_1 (if e_1 e_2 e_3))
   (if (subst x_1 v_1 e_1)
             (subst x_1 v_1 e_2)
             (subst x_1 v_1 e_3))]
  [(subst x_1 v_1 (e_1 e_2))
   ((subst x_1 v_1 e_1) (subst x_1 v_1 e_2))]
  [(subst x_1 v_1 (lambda (x_1) e_1))
   (lambda (x_1) e_1)]
  [(subst x_1 v_1 (lambda (x_2) e_1)) ; capture avoiding substitution
   ,(term-let ([x_21 (variable-not-in (term (v_1 e_1)) (term x_2))])
              (term (lambda (x_21) (subst x_1 v_1 (subst-var x_2 x_21 e_1)))))]
  
  [(subst x_1 v_1 number_1) number_1]
  [(subst x_1 v_1 string_1) string_1]
  [(subst x_1 v_1 x_1) v_1]
  [(subst x_1 v_1 x_2) x_2])
    

(define-metafunction λtss
  subst-var : x x any -> e
  [(subst-var x_1 x_2 x_1) x_2]
  [(subst-var x_1 x_2 (any_1 ...)) ((subst-var x_1 x_2 any_1) ...)]
  [(subst-var x_1 x_2 any_1) any_1])


(define red
  (reduction-relation 
   λtss
   (--> (in-hole E  (equal? v_1 v_2))
        (in-hole E ,(equal? (term v_1) (term v_2))))
   (--> (in-hole E (typeof number_1))
        (in-hole E "number"))
   (--> (in-hole E (typeof string_1))
        (in-hole E "string"))
   (--> (in-hole E (typeof #t))
        (in-hole E "boolean"))
   (--> (in-hole E (typeof #f))
        (in-hole E "boolean"))
   (--> (in-hole E (typeof (lambda (x_1) e_1)))
        (in-hole E "function"))
   (--> (in-hole E (if #t e_1 e_2))
        (in-hole E e_1))
   (--> (in-hole E (if #f e_1 e_2))
        (in-hole E e_2))
   (--> (in-hole E (let (x_1 v_1) e_1))
        (in-hole E (subst x_1 v_1 e_1))
        "let")
   (--> (in-hole E (+ number_1))
        (in-hole E (number_1 +)))
   (--> (in-hole E (++ string_1))
        (in-hole E (string_1 ++)))
   (--> (in-hole E ((string_1 ++) string_2))
        (in-hole E ,(string-append (term string_1) (term string_2))))
   (--> (in-hole E ((number_1 +) number_2))
        (in-hole E ,(+ (term number_1) (term number_2))))
   (--> (in-hole E ((lambda (x_1) e_1) v_1))
        (in-hole E (subst x_1 v_1 e_1)))))


(define generic-add
  (term (lambda (x)
          (if (equal? (typeof x) "number")
              ((+ x) 1)
              (if (equal? (typeof x) "string")
                  ((++ x) "hello")
                  x)))))

(define e1
  (term (let (generic-add ,generic-add)
          (generic-add "hello"))))

(traces red e1)
