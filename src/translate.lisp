; hash tables to remember output for knowns (so that bushys) can print the axiom without rendering it again
(defparameter *k* (make-hash-table :test #'equal))
; dependences of knowns on other knowns
(defparameter *dk* (make-hash-table :test #'equal))
(defparameter *useeval* t) ; if this is set to nil, then throw 'skip whenever eval_m_n, var_m_n or all_n would be used; command line option -skipeval
(defparameter *skipk* (make-hash-table :test #'equal)) ; if we are skipping some, then remember they were skipped so we can skip the bushies that depend on skipped.

(defparameter *o* (make-hash-table :test #'equal)) ; objects with a type (only for thf)
(defparameter *kodeps* (make-hash-table :test #'equal)) ; dependence of known on objects (only for thf)
(defparameter *do* (make-hash-table :test #'equal)) ; dependence of object on objects (only for thf)

(defparameter *recdepskip* nil) ; if t (command line -recdepskip), then bushy problems are not created for problems where a dependency was skipped; otherwise the bushy problem is created but without axioms that were skipped (so probably unprovable)

(defparameter *m* nil)

(defun tp-arity (x)
  (if (and (consp x) (cdr x))
      (1+ (tp-arity (cdr x)))
    0))

(defun tm-str-sexpr (m bvl pvl)
  (if (consp m)
      (cond ((stringp (car m))
             (if (member (car m) bvl :test #'equal)
                 (if (cdr m)
                                        ; this should never happen with a setvar and only setvars should be in bvl
                     (break)
                   (if *useeval*
                       (let ((n (length bvl))
                             (i (position m (reverse bvl) :test #'equal)))
                         (format nil "(var ~d ~d)" i n))
                     (throw 'skip 'var)))
               (let ((a (assoc (car m) pvl :test #'equal)))
                 (if a
                     (let ((ar (tp-arity (cdr a)))) ; arity should correspond to spine length
                       (if (not (= ar (length (cdr m))))
                           (break)
                                        ; Assume eval_i_n shifts X (expecting i args) into ctx with n vars using the given i classes which depend on n vars and gives the appropriate class
                                        ; Special case when i=0: eval_0_n takes a class X and converts it into the class {(x0,..,x_{n-1},y) | y :e X}
                         (if *useeval*
                             (format nil "(eval_~d_~d \"X~d\"~d)" ar (length bvl) (car m) (spine-str-sexpr (cdr m) bvl pvl))
                           (throw 'skip 'eval))))
                   (if (cdr m) ; otherwise a constant; assume constants are prepared to work in any context
                       (format nil "(\"c~d\"~d)" (car m) (spine-str-sexpr (cdr m) bvl pvl))
                     (format nil "\"c~d\"" (car m)))))))
            ((eq (car m) 'FN) (fn-str-sexpr (cdr m) bvl pvl))
            ((eq (car m) '!) (forall-str-sexpr (cdr m) bvl pvl))
            (t (setq *m* m) (break) (format nil "?~S?" m)))
    (if (member m bvl :test #'equal)
        (if *useeval*
            (let ((n (length bvl))
                  (i (position m (reverse bvl) :test #'equal)))
              (format nil "(var_~d_~d)" i n))
          (throw 'skip 'var))
      (let ((a (assoc m pvl :test #'equal)))
        (if a
            (let ((ar (tp-arity (cdr a)))) ; it's not applied so should be arity 0
              (if (> ar 0)
                  (break)
                (format nil "\"X~d\"" m)))
          (format nil "\"c~d\"" m))))))

(defun fn-str-sexpr (ml bvl pvl)
  (if (cdr ml)
      (let ((x (caar ml)))
        (fn-str-sexpr (cdr ml) (cons x bvl) pvl)) ; the "lambda" can be transparent here, i.e., not change the class
    (tm-str-sexpr (car ml) bvl pvl)))

(defun forall-str-sexpr (ml bvl pvl)
  (if (cdr ml)
      (if *useeval*
          (let ((x (caar ml)))
            (format nil "(all_~d ~d)" (length bvl) (forall-str-sexpr (cdr ml) (cons x bvl) pvl)))
        (throw 'skip 'all))
    (tm-str-sexpr (car ml) bvl pvl)))

(defun spine-str-sexpr (s bvl pvl &optional (sep " "))
  (if s
      (format nil "~d~d~d" sep (tm-str-sexpr (car s) bvl pvl) (spine-str-sexpr (cdr s) bvl pvl " "))
    ""))

(defun prop-str-sexpr (p pvl)
  (format nil "(p ~d)" (tm-str-sexpr p nil pvl)))

(defun ax-str-sexpr-2 (vl p pvl)
  (if vl
      (let ((x (caar vl)))
        (format nil "(! \"X~d\" ~d)" x (ax-str-sexpr-2 (cdr vl) p (acons x (cadar vl) pvl))))
    (ax-str-sexpr p pvl)))

(defun ax-str-sexpr (p pvl)
  (if (consp p)
      (cond ((equal (car p) '!!) (ax-str-sexpr-2 (cadr p) (cddr p) pvl))
            ((cdr p) (format nil "(=> ~d ~d)" (prop-str-sexpr (car p) pvl) (ax-str-sexpr (cdr p) pvl)))
            (t (prop-str-sexpr (car p) pvl)))
    (prop-str-sexpr p pvl)))

(defun thm-str-sexpr-2 (svcx concl pvl)
  (if svcx
      (let ((x (caar svcx)))
        (format nil "(! \"X~d\" ~d)" x (thm-str-sexpr-2 (cdr svcx) concl (acons x '("setvar") pvl))))
    (prop-str-sexpr concl pvl)))

(defun thm-str-sexpr (vcx hcx svcx concl pvl)
  (if vcx
      (let ((x (caar vcx)))
        (format nil "(! \"X~d\" ~d)" x (thm-str-sexpr (cdr vcx) hcx svcx concl (acons x (cadar vcx) pvl))))
    (if hcx
        (format nil "(=> ~d ~d)" (prop-str-sexpr (cadar hcx) pvl) (thm-str-sexpr nil (cdr hcx) svcx concl pvl))
      (thm-str-sexpr-2 svcx concl pvl))))

                                        ; here the m could be a class, a prop or a setvar in ctx bvl
                                        ; each is translated to a class without dependence on bvl
(defun tm-str (m bvl pvl)
  (if (consp m)
      (cond ((stringp (car m))
             (if (member (car m) bvl :test #'equal)
                 (if (cdr m)
                                        ; this should never happen with a setvar and only setvars should be in bvl
                     (break)
                   (if *useeval*
                       (let ((n (length bvl))
                             (i (position m (reverse bvl) :test #'equal)))
                         (format nil "var_~d_~d" i n))
                     (throw 'skip 'var)))
               (let ((a (assoc (car m) pvl :test #'equal)))
                 (if a
                     (let ((ar (tp-arity (cdr a)))) ; arity should correspond to spine length
                       (if (not (= ar (length (cdr m))))
                           (break)
                                        ; Assume eval_i_n shifts X (expecting i args) into ctx with n vars using the given i classes which depend on n vars and gives the appropriate class
                                        ; Special case when i=0: eval_0_n takes a class X and converts it into the class {(x0,..,x_{n-1},y) | y :e X}
                         (if *useeval*
                             (format nil "eval_~d_~d(X~d~d)" ar (length bvl) (car m) (spine-str (cdr m) bvl pvl ","))
                           (throw 'skip 'eval))))
                   (if (cdr m) ; otherwise a constant; assume constants are prepared to work in any context
                       (format nil "c~d(~d)" (car m) (spine-str (cdr m) bvl pvl))
                     (format nil "c~d" (car m)))))))
            ((eq (car m) 'FN) (fn-str (cdr m) bvl pvl))
            ((eq (car m) '!) (forall-str (cdr m) bvl pvl))
            (t (setq *m* m) (break) (format nil "?~S?" m)))
    (if (member m bvl :test #'equal)
        (if *useeval*
            (let ((n (length bvl))
                  (i (position m (reverse bvl) :test #'equal)))
              (format nil "var_~d_~d" i n))
          (throw 'skip 'var))
      (let ((a (assoc m pvl :test #'equal)))
        (if a
            (let ((ar (tp-arity (cdr a)))) ; it's not applied so should be arity 0
              (if (> ar 0)
                  (break)
                (format nil "X~d" m)))
          (format nil "c~d" m))))))

(defun fn-str (ml bvl pvl)
  (if (cdr ml)
      (let ((x (caar ml)))
        (fn-str (cdr ml) (cons x bvl) pvl)) ; the "lambda" can be transparent here, i.e., not change the class
    (tm-str (car ml) bvl pvl)))

(defun forall-str (ml bvl pvl)
  (if (cdr ml)
      (if *useeval*
          (let ((x (caar ml)))
            (format nil "all_~d(~d)" (length bvl) (forall-str (cdr ml) (cons x bvl) pvl)))
        (throw 'skip 'all))
    (tm-str (car ml) bvl pvl)))

(defun spine-str (s bvl pvl &optional (sep ""))
  (if s
      (format nil "~d~d~d" sep (tm-str (car s) bvl pvl) (spine-str (cdr s) bvl pvl ","))
    ""))

;(defun bvl-spine-str (bvl &optional (sep ""))
;  (if bvl
;      (format nil "~dX~d~d" sep (car bvl) (bvl-spine-str (cdr bvl) ","))
;    ""))

(defun prop-str (p pvl)
  (format nil "p(~d)" (tm-str p nil pvl)))

(defun ax-str-2 (vl p pvl)
  (if vl
      (let ((x (caar vl)))
        (format nil "(! [X~d] : ~d)" x (ax-str-2 (cdr vl) p (acons x (cadar vl) pvl))))
    (ax-str p pvl)))

(defun ax-str (p pvl)
  (if (consp p)
      (cond ((equal (car p) '!!) (ax-str-2 (cadr p) (cddr p) pvl))
            ((cdr p) (format nil "(~d => ~d)" (prop-str (car p) pvl) (ax-str (cdr p) pvl)))
            (t (prop-str (car p) pvl)))
    (prop-str p pvl)))

(defun thm-str-2 (svcx concl pvl)
  (if svcx
      (let ((x (caar svcx)))
        (format nil "(! [X~d] : ~d)" x (thm-str-2 (cdr svcx) concl (acons x '("setvar") pvl))))
    (prop-str concl pvl)))

(defun thm-str (vcx hcx svcx concl pvl)
  (if vcx
      (let ((x (caar vcx)))
        (format nil "(! [X~d] : ~d)" x (thm-str (cdr vcx) hcx svcx concl (acons x (cadar vcx) pvl))))
    (if hcx
        (format nil "(~d => ~d)" (prop-str (cadar hcx) pvl) (thm-str nil (cdr hcx) svcx concl pvl))
      (thm-str-2 svcx concl pvl))))

(defun fof-tm-skip-kdeps (m)
  (if (consp m)
      (cond ((stringp (car m))
             (let ((h (car m)))
               (when (gethash h *skipk*) (throw 'skip 'kdep))
               (dolist (a (cdr m)) (fof-tm-skip-kdeps a))))
            ((eq (car m) 'FN) (fof-fn-skip-kdeps (cdr m)))
            ((eq (car m) '!) (fof-forall-skip-kdeps (cdr m)))
            ((eq (car m) 'FORGET) (fof-forget-skip-kdeps (cdadr m)))
            ((eq (car m) 'USES) (dolist (a (cdr m)) (fof-tm-skip-kdeps a)))
            (t (break)))
    (when (stringp m)
      (when (gethash m *skipk*) (throw 'skip 'kdep)))))

(defun fof-fn-skip-kdeps (ml)
  (if (cdr ml)
      (fof-fn-skip-kdeps (cdr ml))
    (fof-tm-skip-kdeps (car ml))))

(defun fof-forall-skip-kdeps (ml)
  (if (cdr ml)
      (fof-forall-skip-kdeps (cdr ml))
    (fof-tm-skip-kdeps (car ml))))

(defun fof-forget-skip-kdeps (ml)
  (if (cdr ml)
      (fof-forget-skip-kdeps (cdr ml))
    (fof-tm-skip-kdeps (car ml))))

(defun fof-tm-kdeps (g m)
  (if (consp m)
      (cond ((stringp (car m))
             (let ((h (car m)))
               (when (gethash h *k*)
                 (unless (gethash h *dk*)
                   (setf (gethash h *dk*) t)
                   (format g "~d~%" (gethash h *k*))))
               (dolist (a (cdr m)) (fof-tm-kdeps g a))))
            ((eq (car m) 'FN) (fof-fn-kdeps g (cdr m)))
            ((eq (car m) '!) (fof-forall-kdeps g (cdr m)))
            ((eq (car m) 'FORGET) (fof-forget-kdeps g (cdadr m)))
            ((eq (car m) 'USES) (dolist (a (cdr m)) (fof-tm-kdeps g a)))
            (t (break)))
    (when (stringp m)
      (when (gethash m *k*)
        (unless (gethash m *dk*)
          (setf (gethash m *dk*) t)
          (format g "~d~%" (gethash m *k*)))))))

(defun fof-fn-kdeps (g ml)
  (if (cdr ml)
      (fof-fn-kdeps g (cdr ml))
    (fof-tm-kdeps g (car ml))))

(defun fof-forall-kdeps (g ml)
  (if (cdr ml)
      (fof-forall-kdeps g (cdr ml))
    (fof-tm-kdeps g (car ml))))

(defun fof-forget-kdeps (g ml)
  (if (cdr ml)
      (fof-forget-kdeps g (cdr ml))
    (fof-tm-kdeps g (car ml))))

(defun translatev1 (fn g2n probdir)
  (let ((f (open fn :direction :input))
        (g2 (open g2n :direction :output :if-exists :supersede))
        (l nil))
    (loop while (setq l (read f nil nil)) do
      (when (and (consp l) (not (eq (car l) 'SORT)))
        (case (car l)
              (TERM nil)
              (AXIOM
               (let ((nm (cadr l)) (p (nth 2 l)))
                 (setf (gethash nm *skipk*) t) ; assume we're skipping it until we're sure we won't skip it
                 (catch 'skip
                   (setf (gethash nm *k*) (format nil "fof(a~d_ax,axiom,~d)." nm (ax-str p nil)))
                   (setf (gethash nm *skipk*) nil) ; since skip was not thrown, we're not skipping it
                   (format g2 "~d~%" (gethash nm *k*)))))
              (THEOREM
               (let ((nm (cadr l))
                     (vcx (nth 2 l))
                     (hcx (nth 3 l))
                     (svcx (nth 4 l))
                     (concl (nth 5 l))
                     (pf (nth 6 l)))
                 (setf (gethash nm *skipk*) t) ; assume we're skipping it until we're sure we won't skip it
                 (catch 'skip
                   (setf (gethash nm *k*) (format nil "fof(a~d_thm,axiom,~d)." nm (thm-str (cdr vcx) (cdr hcx) (cdr svcx) concl nil)))
                   (setf (gethash nm *skipk*) nil) ; since skip was not thrown, we're not skipping it
                   (format g2 "~d~%" (gethash nm *k*))
                   (when *recdepskip* (fof-tm-skip-kdeps pf)) ; this throws skip before making the bushy problem if a dependency was skipped
                   (let ((g (open (format nil "~d/~d.p" probdir nm) :direction :output :if-exists :supersede)))
                     (setq *dk* (make-hash-table :test #'equal))
                     (fof-tm-kdeps g pf)
                     (format g "fof(a~d_thm,conjecture,~d).~%" nm (thm-str (cdr vcx) (cdr hcx) (cdr svcx) concl nil))
                     (close g)))))
              (t nil))))
    (close f)
    (close g2))
  (sb-ext:exit :code 0))

(defun translatev2 (fn g2n probdir)
  (let ((f (open fn :direction :input))
        (g2 (open g2n :direction :output :if-exists :supersede))
        (l nil))
    (loop while (setq l (read f nil nil)) do
      (when (and (consp l) (not (eq (car l) 'SORT)))
        (case (car l)
              (TERM nil)
              (AXIOM
               (let ((nm (cadr l)) (p (nth 2 l)))
                 (setf (gethash nm *skipk*) t) ; assume we're skipping it until we're sure we won't skip it
                 (catch 'skip
                   (setf (gethash nm *k*) (format nil "(axiom \"~d\" ~d)" nm (ax-str-sexpr p nil)))
                   (setf (gethash nm *skipk*) nil) ; since skip was not thrown, we're not skipping it
                   (format g2 "~d~%" (gethash nm *k*)))))
              (THEOREM
               (let ((nm (cadr l))
                     (vcx (nth 2 l))
                     (hcx (nth 3 l))
                     (svcx (nth 4 l))
                     (concl (nth 5 l))
                     (pf (nth 6 l)))
                 (setf (gethash nm *skipk*) t) ; assume we're skipping it until we're sure we won't skip it
                 (catch 'skip
                   (setf (gethash nm *k*) (format nil "(axiom \"~d\" ~d)" nm (thm-str-sexpr (cdr vcx) (cdr hcx) (cdr svcx) concl nil)))
                   (setf (gethash nm *skipk*) nil) ; since skip was not thrown, we're not skipping it
                   (format g2 "~d~%" (gethash nm *k*))
                   (when *recdepskip* (fof-tm-skip-kdeps pf)) ; this throws skip before making the bushy problem if a dependency was skipped
                   (let ((g (open (format nil "~d/~d.p" probdir nm) :direction :output :if-exists :supersede)))
                     (setq *dk* (make-hash-table :test #'equal))
                     (fof-tm-kdeps g pf)
                     (format g "(conjecture \"~d\" ~d)~%" nm (thm-str-sexpr (cdr vcx) (cdr hcx) (cdr svcx) concl nil))
                     (close g)))))
              (t nil))))
    (close f)
    (close g2))
  (sb-ext:exit :code 0))

(defun translatev2forivy (fn g2n probdir ivydir)
  (let ((f (open fn :direction :input))
        (g2 (open g2n :direction :output :if-exists :supersede))
        (l nil))
    (loop while (setq l (read f nil nil)) do
      (when (and (consp l) (not (eq (car l) 'SORT)))
        (case (car l)
              (TERM nil)
              (AXIOM
               (let ((nm (cadr l)) (p (nth 2 l)))
                 (setf (gethash nm *skipk*) t) ; assume we're skipping it until we're sure we won't skip it
                 (catch 'skip
                   (setf (gethash nm *k*) (format nil "(axiom \"~d\" ~d)" nm (ax-str-sexpr p nil)))
                   (setf (gethash nm *skipk*) nil) ; since skip was not thrown, we're not skipping it
                   (format g2 "~d~%" (gethash nm *k*)))))
              (THEOREM
               (let ((nm (cadr l))
                     (vcx (nth 2 l))
                     (hcx (nth 3 l))
                     (svcx (nth 4 l))
                     (concl (nth 5 l))
                     (pf (nth 6 l)))
                 (setf (gethash nm *skipk*) t) ; assume we're skipping it until we're sure we won't skip it
                 (catch 'skip
                   (setf (gethash nm *k*) (format nil "(axiom \"~d\" ~d)" nm (thm-str-sexpr (cdr vcx) (cdr hcx) (cdr svcx) concl nil)))
                   (setf (gethash nm *skipk*) nil) ; since skip was not thrown, we're not skipping it
                   (when (probe-file (format nil "~d/~d.p" ivydir nm))
                     (format g2 "~d~%" (gethash nm *k*))
                     (when *recdepskip* (fof-tm-skip-kdeps pf)) ; this throws skip before making the bushy problem if a dependency was skipped
                     (let ((g (open (format nil "~d/~d.p" probdir nm) :direction :output :if-exists :supersede)))
                       (setq *dk* (make-hash-table :test #'equal))
                       (fof-tm-kdeps g pf)
                       (format g "(conjecture \"~d\" ~d)~%" nm (thm-str-sexpr (cdr vcx) (cdr hcx) (cdr svcx) concl nil))
                       (close g))))))
              (t nil))))
    (close f)
    (close g2))
  (sb-ext:exit :code 0))

; thf code
(defparameter *interpreted-thf* (list
  (list "wtru" nil 0 #'(lambda () "$true"))
  (list "wfal" nil 0 #'(lambda () "$false"))
  (list "wn" nil 1 #'(lambda (x) (format nil "(~~ ~d)" x)))
  (list "wi" nil 2 #'(lambda (x y) (format nil "(~d => ~d)" x y)))
  (list "wb" nil 2 #'(lambda (x y) (format nil "(~d <=> ~d)" x y)))
  (list "wo" nil 2 #'(lambda (x y) (format nil "(~d | ~d)" x y)))
  (list "wa" nil 2 #'(lambda (x y) (format nil "(~d & ~d)" x y)))
  (list "wnan" nil 2 #'(lambda (x y) (format nil "(~~ (~d & ~d))" x y)))
  (list "wxo" nil 2 #'(lambda (x y) (format nil "(~~ (~d <=> ~d))" x y)))
  (list "wif" nil 3 #'(lambda (x y z) (format nil "((~d & ~d) | ((~~ ~d) & ~d))" x y x z)))
  (list "w3o" nil 3 #'(lambda (x y z) (format nil "(~d | ~d | ~d)" x y z)))
  (list "w3a" nil 3 #'(lambda (x y z) (format nil "(~d & ~d & ~d)" x y z)))
  (list "whad" nil 3 #'(lambda (x y z) (format nil "(~~ ((~~ (~d <=> ~d)) <=> ~d))" x y z)))
  (list "wcad" nil 3 #'(lambda (x y z) (format nil "((~d & ~d) | (~d & (~~ (~d <=> ~d))))" x y z x y)))
  ; (list "wnf" nil 1 #'(lambda (x) (format nil "((? [X:$i] : (~d @ X)) => (! [X:$i] : (~d @ X)))" x x)))
  ; (list "wsb" nil 2 #'(lambda (ph x) (format nil "(~d @ ~d)" ph x)))
  ; (list "cab" nil 1 #'(lambda (p) p))
  (list "wceq" nil 2 #'(lambda (x y) (format nil "(~d = ~d)" x y)))
  (list "wne" nil 2 #'(lambda (x y) (format nil "(~d != ~d)" x y)))
  (list "wnel" nil 2 #'(lambda (x y) (format nil "(~~ (wcel @ ~d @ ~d))" x y)))
  ; (list "wal" 'BIND1 #'(lambda (m) (caar (cdadr m))) #'(lambda (m) (cadr (cdadr m))) #'(lambda (x body) (format nil "(! [X~d:$i] : ~d)" x body)))
  ; (list "wex" 'BIND1 #'(lambda (m) (caar (cdadr m))) #'(lambda (m) (cadr (cdadr m))) #'(lambda (x body) (format nil "(? [X~d:$i] : ~d)" x body)))
  ))

(defun tp0-str (x) (cond ((equal x "setvar") "$i") ((equal x "class") "($i > $o)") ((equal x "wff") "$o") (t (break))))
(defun tp-str (x) (if (consp x) (if (cdr x) (format nil "(~d > ~d)" (tp0-str (car x)) (tp-str (cdr x))) (tp0-str (car x))) (break)))
(defun tp2-str (x) (if (consp x) (if (cdr x) (format nil "(~d > ~d)" (tp-str (car x)) (tp2-str (cdr x))) (tp-str (car x))) (break)))

(defun tm-thf-str (m bvl)
  (if (consp m)
      (cond ((stringp (car m))
             (if (member (car m) bvl :test #'equal)
                 (if (cdr m)
                     (format nil "(X~d~d)" (car m) (spine-thf-str (cdr m) bvl))
                   (format nil "X~d" (car m)))
               (let ((a (assoc (car m) *interpreted-thf* :test #'equal)))
                 (if a
                     (if (cadr a)
                         (cond ((eq (cadr a) 'BIND1) ; binder of 1 var
                                (let ((x (funcall (caddr a) m))
                                      (body (funcall (cadddr a) m))
                                      (strf (nth 4 a)))
                                  (funcall strf x (tm-thf-str body (cons x bvl)))))
                               (t ; unknown case
                                (break)))
                                        ; ordinary case
                       (let ((arity (caddr a))
                             (strf (cadddr a)))
                         (unless (equal (length (cdr m)) arity) (setq *m* m) (break))
                         (apply strf
                                (mapcar #'(lambda (n) (tm-thf-str n bvl)) (cdr m)))))
                   (if (cdr m)
                       (format nil "(c~d~d)" (car m) (spine-thf-str (cdr m) bvl))
                     (format nil "c~d" (car m)))))))
            ((eq (car m) 'FN) (fn-thf-str (cdr m) bvl))
            ((eq (car m) '!) (forall-thf-str (cdr m) bvl))
            (t (setq *m* m) (break) (format nil "?~S?" m)))
    (cond ((equal m "wtru") "$true")
          ((equal m "wfal") "$false")
          (t
           (if (member m bvl :test #'equal)
               (format nil "X~d" m)
             (format nil "c~d" m))))))

(defun fn-thf-str (ml bvl)
  (if (cdr ml)
      (let ((x (caar ml)))
        (format nil "(^ [X~d:~d] : ~d)" x (tp0-str (cadar ml)) (fn-thf-str (cdr ml) (cons x bvl))))
    (tm-thf-str (car ml) bvl)))

(defun forall-thf-str (ml bvl)
  (if (cdr ml)
      (let ((x (caar ml)))
        (format nil "(! [X~d:~d] : ~d)" x (tp0-str (cadar ml)) (forall-thf-str (cdr ml) (cons x bvl))))
    (tm-thf-str (car ml) bvl)))

(defun spine-thf-str (s bvl)
  (if s
      (format nil " @ ~d~d" (tm-thf-str (car s) bvl) (spine-thf-str (cdr s) bvl))
    ""))

(defun ax-thf-str-2 (vl p bvl)
  (if vl
      (let ((x (caar vl)))
        (format nil "(! [X~d:~d] : ~d)" x (tp-str (cadar vl)) (ax-thf-str-2 (cdr vl) p (cons x bvl))))
    (ax-thf-str p bvl)))

(defun ax-thf-str (p bvl)
  (if (consp p)
      (cond ((equal (car p) '!!) (ax-thf-str-2 (cadr p) (cddr p) bvl))
            ((cdr p) (format nil "(~d => ~d)" (tm-thf-str (car p) bvl) (ax-thf-str (cdr p) bvl)))
            (t (tm-thf-str (car p) bvl)))
    (tm-thf-str p bvl)))

(defun thm-thf-str (vcx hcx svcx concl bvl)
  (if vcx
      (let ((x (caar vcx)))
        (format nil "(! [X~d:~d] : ~d)" x (tp-str (cadar vcx)) (thm-thf-str (cdr vcx) hcx svcx concl (cons x bvl))))
    (if hcx
        (format nil "(~d => ~d)" (tm-thf-str (cadar hcx) bvl) (thm-thf-str nil (cdr hcx) svcx concl bvl))
      (if svcx
          (let ((x (caar svcx)))
            (format nil "(! [X~d:$i] : ~d)" x (thm-thf-str nil nil (cdr svcx) concl (cons x bvl))))
        (tm-thf-str concl bvl)))))

(defun thf-tm-odeps (g m)
  (if (consp m)
      (cond ((stringp (car m))
             (let ((h (car m)))
               (when (gethash h *o*)
                 (unless (gethash h *do*)
                   (setf (gethash h *do*) t)
                   (format g "~d~%" (gethash h *o*))))
               (dolist (a (cdr m)) (thf-tm-odeps g a))))
            ((eq (car m) 'FN) (thf-fn-odeps g (cdr m)))
            ((eq (car m) '!) (thf-forall-odeps g (cdr m)))
            ((eq (car m) 'FORGET) (thf-forget-odeps g (cdadr m)))
            ((eq (car m) 'USES) (dolist (a (cdr m)) (thf-tm-odeps g a)))
            (t (break)))
    (when (stringp m)
      (when (gethash m *o*)
        (unless (gethash m *do*)
          (setf (gethash m *do*) t)
          (format g "~d~%" (gethash m *o*)))))))

(defun thf-fn-odeps (g ml)
  (if (cdr ml)
      (thf-fn-odeps g (cdr ml))
    (thf-tm-odeps g (car ml))))

(defun thf-forall-odeps (g ml)
  (if (cdr ml)
      (thf-forall-odeps g (cdr ml))
    (thf-tm-odeps g (car ml))))

(defun thf-forget-odeps (g ml)
  (if (cdr ml)
      (thf-forget-odeps g (cdr ml))
    (thf-tm-odeps g (car ml))))

(defun thf-tm-kdeps (g m)
  (if (consp m)
      (cond ((stringp (car m))
             (let ((h (car m)))
               (when (gethash h *k*)
                 (unless (gethash h *dk*)
                   (setf (gethash h *dk*) t)
                   (dolist (o (gethash h *kodeps*))
                     (unless (gethash o *do*)
                       (setf (gethash o *do*) t)
                       (format g "~d~%" (gethash o *o*))))
                   (format g "~d~%" (gethash h *k*))))
               (dolist (a (cdr m)) (thf-tm-kdeps g a))))
            ((eq (car m) 'FN) (thf-fn-kdeps g (cdr m)))
            ((eq (car m) '!) (thf-forall-kdeps g (cdr m)))
            ((eq (car m) 'FORGET) (thf-forget-kdeps g (cdadr m)))
            ((eq (car m) 'USES) (dolist (a (cdr m)) (thf-tm-kdeps g a)))
            (t (break)))
    (when (stringp m)
      (when (gethash m *k*)
        (unless (gethash m *dk*)
          (setf (gethash m *dk*) t)
          (dolist (o (gethash m *kodeps*))
            (unless (gethash o *do*)
              (setf (gethash o *do*) t)
              (format g "~d~%" (gethash o *o*))))
          (format g "~d~%" (gethash m *k*)))))))

(defun thf-fn-kdeps (g ml)
  (if (cdr ml)
      (thf-fn-kdeps g (cdr ml))
    (thf-tm-kdeps g (car ml))))

(defun thf-forall-kdeps (g ml)
  (if (cdr ml)
      (thf-forall-kdeps g (cdr ml))
    (thf-tm-kdeps g (car ml))))

(defun thf-forget-kdeps (g ml)
  (if (cdr ml)
      (thf-forget-kdeps g (cdr ml))
    (thf-tm-kdeps g (car ml))))

(defun thf-ax-odeps (g p)
  (if (consp p)
      (cond ((equal (car p) '!!) (thf-ax-odeps g (cddr p)))
            ((cdr p)
             (thf-tm-odeps g (car p))
             (thf-ax-odeps g (cdr p)))
            (t (thf-tm-odeps g (car p))))
    (thf-tm-odeps g p)))

(defun translatethfv3 (fn g2n probdir)
  (let ((f (open fn :direction :input))
        (g2 (open g2n :direction :output :if-exists :supersede))
        (l nil))
    (loop while (setq l (read f nil nil)) do
      (when (and (consp l) (not (eq (car l) 'SORT)))
        (case (car l)
              (TERM
               (let ((nm (cadr l))
                     (tp (caddr l)))
                 (unless (member nm (mapcar #'car *interpreted-thf*) :test #'equal)
                   (setf (gethash nm *o*) (format nil "thf(c~d_tp,type,(c~d : ~d))." nm nm (tp2-str tp)))
                   (format g2 "~d~%" (gethash nm *o*)))))
              (AXIOM
               (let ((nm (cadr l)) (p (nth 2 l)))
                 (setf (gethash nm *k*) (format nil "thf(a~d_ax,axiom,~d)." nm (ax-thf-str p nil)))
                 (format g2 "~d~%" (gethash nm *k*))
                 (setq *do* (make-hash-table :test #'equal))
                 (thf-ax-odeps nil p)
                 (let ((ol nil))
                   (maphash #'(lambda (o v) (declare (ignore v)) (push o ol)) *do*)
                   (setf (gethash nm *kodeps*) ol))))
              (THEOREM
               (let ((nm (cadr l))
                     (vcx (nth 2 l))
                     (hcx (nth 3 l))
                     (svcx (nth 4 l))
                     (concl (nth 5 l))
                     (pf (nth 6 l)))
                 (setf (gethash nm *k*) (format nil "thf(a~d_thm,axiom,~d)." nm (thm-thf-str (cdr vcx) (cdr hcx) (cdr svcx) concl nil)))
                 (format g2 "~d~%" (gethash nm *k*))
                 (let ((g (open (format nil "~d/~d.p" probdir nm) :direction :output :if-exists :supersede)))
                   (setq *do* (make-hash-table :test #'equal))
                   (setq *dk* (make-hash-table :test #'equal))
                   (dolist (h (cdr hcx))
                     (thf-tm-odeps g (cadr h)))
                   (thf-tm-odeps g concl)
                   (thf-tm-odeps g pf)
                   (let ((ol nil))
                     (maphash #'(lambda (o v) (declare (ignore v)) (push o ol)) *do*)
                     (setf (gethash nm *kodeps*) ol))
                   (thf-tm-kdeps g pf)
                   (format g "thf(a~d_thm,conjecture,~d).~%" nm (thm-thf-str (cdr vcx) (cdr hcx) (cdr svcx) concl nil))
                   (close g))))
              (t nil))))
    (close f)
    (close g2))
  (sb-ext:exit :code 0))

(defun top ()
  (when (member "-skipeval" sb-ext:*posix-argv* :test #'equal) (setq *useeval* nil))
  (when (member "-recdepskip" sb-ext:*posix-argv* :test #'equal) (setq *recdepskip* t))
  (let ((l '(("tofof" #'translatev1 3 "tofof <inputfile> <outputaxfile> <outputbushydir>")
             ("tolisp" #'translatev2 3 "tolisp <inputfile> <outputaxfile> <outputbushydir>")
             ("tolispforivy" #'translatev2forivy 4 "tolisp <inputfile> <outputaxfile> <outputbushydir> <ivydir>")
             ("tothfv3" #'translatethfv3 3 "tothfv3 <inputfile> <outputaxfile> <outputbushydir>")
             )))
    (dolist (x l)
      (let ((c (member (car x) sb-ext:*posix-argv* :test #'equal)))
        (when c
          (unless (= (length (cdr c)) (caddr x))
            (format t "Usage: ~d~%" (cadddr x))
            (sb-ext:exit :code 1))
          (apply (eval (cadr x)) (cdr c)))))
    (format t "Expected one of these commands: ~d~%" (mapcar #'car l))
    (sb-ext:exit :code 1)))

(sb-ext:save-lisp-and-die "translate" :executable t :toplevel #'top)
