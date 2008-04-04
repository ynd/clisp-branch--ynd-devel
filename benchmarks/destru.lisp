;;; DESTRU -- Destructive operation benchmark

;;; patch for length

;(defun length (x) (list-length x))  ??? cheating

(defun destructive (n m)
  (declare (type fixnum n m))
  (let ((l (do ((i 10. (the fixnum (1- i)))
                (a () (push () a)))
               ((= (the fixnum i) 0) a)
             (declare (type fixnum i)))))
    (do ((i n (the fixnum (1- i))))
        ((= (the fixnum i) 0))
      (declare (type fixnum i))
      (cond ((null (car l))
             (do ((l l (cdr l)))
                 ((null l))
               (or (car l)
                   (rplaca l (cons () ())))
               (nconc (car l)
                      (do ((j m (the fixnum (1- j)))
                           (a () (push () a)))
                          ((= (the fixnum j) 0) a)
                        (declare (type fixnum j))))))
            (t
             (do ((l1 l (cdr l1))
                  (l2 (cdr l) (cdr l2)))
                 ((null l2))
               (rplacd (do ((j (floor (the fixnum (length (car l2))) 2)
                               (the fixnum (1- j)))
                            (a (car l2) (cdr a)))
                           ((zerop (the fixnum j)) a)
                         (declare (type fixnum j))
                         (rplaca a i))
                       (let ((n (floor (the fixnum (length (car l1))) 2)))
                         (cond ((= (the fixnum n) 0) (rplaca l1 ())
                                (car l1))
                               (t
                                (do ((j n (the fixnum (1- j)))
                                     (a (car l1) (cdr a)))
                                    ((= (the fixnum j) 1)
                                     (prog1 (cdr a)
                                            (rplacd a ())))
                                  (declare (type fixnum j))
                                  (rplaca a i))))))))))))

;;; call:  (destructive 600. 50.)

