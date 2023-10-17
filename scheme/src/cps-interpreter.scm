(import (scheme base)
        (scheme write)
        (scheme read)
        (cyclone match))
    
; read a program in the CPS language from stdin and interpret it, writing the result to stdout
(define (main)
  (display ((evaluate '()) (read)))
  (newline))


(define (evaluate env)
  (define (eval-expr expr)
    (match expr
      (('record (field-access ...) var cnt)
       ((evaluate 
          (bind env var 
            (make-record 
              (list->vector 
                (map eval-fieldaccess field-access)))))
        cnt))

      (('select idx rec var cnt)
       ((evaluate (bind env var (record-ref (eval-val rec) idx)))
        cnt))

      (('offset idx rec var cnt)
       ((evaluate (bind env var (record-ofs (eval-val rec) idx)))
        cnt))

      (('fix ((fname fparams fbody)...) cnt)
       (let ((fixenv (foldl (lambda (fn env) 
                              (cons (cons fn 'uninit) env))  
                            env fname)))
         (let ((procs (map (lambda (p* b) 
                             (lambda args 
                               ((evaluate (bind* fixenv p* args)) b)))                              
                           fparams fbody)))
           (for-each (lambda (var val) (update-env! fixenv var val)) fname procs)
           ((evaluate fixenv) cnt))))
       
      (('switch value arms ...)
       (eval-expr (list-ref arms (eval-val value))))

      (('primop op args vars cnts)
       (error "unimplemented primop" op))

      (('halt val) 
       (eval-val val env))

      (('panic msg)
       (error msg))

      ((f a ...)
       (apply (eval-val f)
              (map eval-val a)))

      (_ (error "unimplemnted expression" expr))))

  (define (eval-fieldaccess fa)
    (match fa
      ((f ap) (apply-accesspath (eval-val f) ap))
      (f (eval-val f))))

  (define (apply-accesspath val ap)
    (match ap
      (('ref 0) val)
      (('ref i) (record-ofs val i))
      (('sel i ap_) (apply-accesspath (record-ref val i) ap_))))

  (define (eval-val expr)
    (match expr
      ((? symbol? name) (lookup name))
      ((? integer? i) i)
      ((? real? r) r)
      ((? string? s) s)
      (_ (error "unimplemnted value" expr))))

  (define (lookup var)
    (match (assoc var env)
      ((_ . val) val)
      (#f (error "unbound variable" var))))

  eval-expr)


(define (update-env! env var val)
  (let ((binding (assoc var env)))
    (if binding
        (set-cdr! binding val) 
        (error "unbound variable" var))))

(define (bind env var val)
  (cons (cons var val) env))

(define (bind* env var* val*)
  (append (map cons var* val*) env))


(define (make-record vec)
  (cons 0 vec))

(define (record-ref rec k)
  (vector-ref (cdr rec) (+ (car rec) k)))

(define (record-ofs rec k)
  (cons (+ k (car rec)) (cdr rec)))


(main)
