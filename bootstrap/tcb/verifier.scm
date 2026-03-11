; verifier.scm - Trace Verifier (~12 lines of core logic)
;
; This is the TRUSTED CORE. Every line must be human-verified.
; Each case directly transcribes a categorical law.

(define (verify-step rule before after)
  (cond
    ; Identity laws: compose f id → f, compose id f → f
    ((eq? rule 'id-right)   (equal? before (list 'compose after 'id)))
    ((eq? rule 'id-left)    (equal? before (list 'compose 'id after)))

    ; Product laws: fst ∘ ⟨f,g⟩ → f, snd ∘ ⟨f,g⟩ → g
    ((eq? rule 'fst-pair)   (and (equal? (car before) 'compose)
                                 (equal? (cadr before) 'fst)
                                 (equal? (car (caddr before)) 'pair)
                                 (equal? after (cadr (caddr before)))))
    ((eq? rule 'snd-pair)   (and (equal? (car before) 'compose)
                                 (equal? (cadr before) 'snd)
                                 (equal? (car (caddr before)) 'pair)
                                 (equal? after (caddr (caddr before)))))

    ; Product eta: ⟨fst, snd⟩ → id
    ((eq? rule 'eta-pair)   (and (equal? before '(pair fst snd))
                                 (equal? after 'id)))

    ; Coproduct laws: [f,g] ∘ inl → f, [f,g] ∘ inr → g
    ((eq? rule 'case-inl)   (and (equal? (car before) 'compose)
                                 (equal? (car (cadr before)) 'case)
                                 (equal? (caddr before) 'inl)
                                 (equal? after (cadr (cadr before)))))
    ((eq? rule 'case-inr)   (and (equal? (car before) 'compose)
                                 (equal? (car (cadr before)) 'case)
                                 (equal? (caddr before) 'inr)
                                 (equal? after (caddr (cadr before)))))

    ; Coproduct eta: [inl, inr] → id
    ((eq? rule 'eta-case)   (and (equal? before '(case inl inr))
                                 (equal? after 'id)))

    ; Terminal: any composition with terminal → terminal
    ((eq? rule 'terminal)   (equal? after 'terminal))

    ; No matching rule
    (else #f)))

(define (verify-trace trace)
  (if (null? trace)
      #t
      (and (verify-step (caar trace) (cadar trace) (caddar trace))
           (verify-trace (cdr trace)))))

; Helper to get third element
(define (caddar x) (car (cdr (cdr (car x)))))

; Main: read trace and verify
(define (main)
  (let ((trace (read)))
    (if (verify-trace trace)
        (display "VERIFIED\n")
        (display "REJECTED\n"))))
