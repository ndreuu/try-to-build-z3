(declare-datatypes ((list 0)) (((nil) (cons (car Int) (cdr list)))))

(declare-fun Inv (list Int Int) Bool)
(declare-fun length (list Int) Bool)

(assert (length nil 0))
(assert (forall ((x Int) (xs list) (n Int))
  (=> (length xs n) (length (cons x xs) (+ n 1)))))

(assert (forall ((y list) (i Int)) (=> (length y i) (Inv y i i))))
(assert (forall ((y list) (i Int) (j Int) (y1 list) (j1 Int) (tmp Int))
  (=> (and (Inv y i j) (length y j) (= y (cons tmp y1)) (length y1 j1)) (Inv y1 (- i 1) j1))))
(assert (forall ((y list) (i Int) (j Int))
  (=> (and (Inv y i j) (length y j) (< i 0)) false)))

(check-sat)
(get-model)

