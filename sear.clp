;; Carulli Antonio Matteo
;; Sistema esperto per l'anamnesi del ritardo nello sviluppo del bambino

;; Default priorities
(defglobal ?*highest-priority* = 1000)
(defglobal ?*high-priority* = 100)
(defglobal ?*low-priority* = -100)
(defglobal ?*lowest-priority* = -1000)

;; Templates

;; Ogni "sintomo", fatto o diagnosi è un OAV.
;; Un OAV è una tripla (Object, Attribute,Value) associata a un Certainty Factor

(deftemplate oav
    (multislot object (type SYMBOL))
    (multislot attribute (type SYMBOL))
    (multislot value (type SYMBOL))
    (slot cf (type FLOAT) (range -1.0 +1.0)))

(deftemplate anamnesi
    (slot stato))

;; Funzioni di supporto

(deffunction get-all-facts-by-names ($?template-names)
    (bind ?facts (create$))
    (progn$ (?f (get-fact-list))
    (if (member$ (fact-relation ?f) $?template-names)
        then (bind ?facts (create$ ?facts ?f))))
?facts)

(deffunction stampa-fatti (?facts)
    (bind ?i 1)
    (printout t crlf "*********************LISTA FATTI*********************" crlf)
    (printout t "(i) object | attribute | value | (cf)" crlf)
    (progn$ (?f ?facts)
    (format t "(%d) %s | %s | %s | (%5.3f)%n" ?i
        (implode$ (fact-slot-value ?f object))
        (implode$ (fact-slot-value ?f attribute))
        (implode$ (fact-slot-value ?f value))
        (fact-slot-value ?f cf))
    (bind ?i (+ ?i 1)))
    (printout t "*****************************************************" crlf))

(deffunction change-oav-by-index (?index ?facts)
    (bind ?f (nth$ ?index ?facts))
    (printout t "Vecchio valore >> Nuovo valore" crlf)
    (format t "object: %s >> object: " (implode$ (fact-slot-value ?f object)))
    (bind ?o (explode$ (lowcase (readline))))
    (format t "attribute: %s >> attribute: " (implode$ (fact-slot-value ?f attribute)))
    (bind ?a (explode$ (lowcase (readline))))
    (format t "value: %s >> value: " (implode$ (fact-slot-value ?f value)))
    (bind ?v (explode$ (lowcase (readline))))
    (format t "cf: %5.3f >> cf: " (fact-slot-value ?f cf))
    (bind ?cf (read))
    (modify ?f (object ?o)(attribute ?a)(value ?v)(cf ?cf)))

(deffunction gen-int-list (?max-n)
    (bind ?int-list (create$))
    (loop-for-count (?i 1 ?max-n)
    (bind ?int-list (create$ ?int-list ?i)))
    ?int-list)

(deffunction ask-question (?question $?allowed-values)
    (bind ?ris (create$ o))
    (bind ?question (str-cat ?question " ns: non so/non ricordo, e: esci, o: opzioni"))
    (while (not (subsetp ?ris (create$ ?allowed-values ns))) do
        (if (not (or (numberp (member$ o ?ris))(numberp (member$ e ?ris))))
        then (printout t crlf "Risposta non valida..." crlf ?question))
        (printout t ?question crlf)
        (printout t " >> ")
        (bind ?ris (explode$ (lowcase (readline))))
        ;;opzioni
        (if (numberp (member$ o ?ris))
        then (bind ?facts (get-all-facts-by-names oav))
            (stampa-fatti ?facts)
            (bind ?r (create$))
            (while (not (or (eq ?r si)(eq ?r no))) do
                (printout t crlf "Modificare un fatto? >> ")
                (bind ?r (read))
                (if (lexemep ?r) then (bind ?r (lowcase ?r))))
            (while (eq ?r si) do
                (bind ?num-facts (length$ ?facts))
                (printout t "Indicare l'indice del fatto da modificare o digitare")
                (printout t " no per tornare indietro >> ")
                (bind ?r (read))
                (create$ (gen-int-list ?num-facts) no)
                (if (numberp ?r) then (change-oav-by-index ?r ?facts)
                    (bind ?facts (get-all-facts-by-names oav))
                    (printout t crlf "Nuova lista fatti:" crlf)
                    (stampa-fatti ?facts))
                (printout t "Modificare un fatto? >> ")
                (bind ?r (read))
                (if (lexemep ?r) then (bind ?r (lowcase ?r))))
        else (if (numberp (member$ e ?ris))
            then (printout t "Halting..." crlf)
                (halt))))
?ris)

;; Funzioni per gestire il Certainty Factor

(deffunction combina-cf (?CF1 ?CF2)
   (if (and (numberp ?CF1)(numberp ?CF2))
    then (if (< (* ?CF1 ?CF2) 0)   ;;se X*Y<0 (X e Y discordi)
        then (bind ?CF (/ (+ ?CF1 ?CF2)(- 1 (min ?CF1 ?CF2))))  ;;(X+Y)/(1-min(X,Y))
        else (if (and (> ?CF1 0)(> ?CF2 0)) ;;se X,Y > 0
            then (bind ?CF (- (+ ?CF1 ?CF2)(* ?CF1 ?CF2)))  ;;X+Y-XY
            else (bind ?CF (+ ?CF1 ?CF2 (* ?CF1 ?CF2))))))   ;;se X,Y <= 0 => X+Y+XY
?CF)

;; Se due fatti uguali hanno cf diversi, combinali

(defrule combina-certainty-factor
    (declare (salience ?*highest-priority*))
    ?fact1 <- (oav (object $?o)
                   (attribute $?a)
                   (value $?v)
                   (cf ?CF1))
    ?fact2 <- (oav (object $?o)
                   (attribute $?a)
                   (value $?v)
                   (cf ?CF2))
    (test (neq ?fact1 ?fact2))
    =>
    (retract ?fact1)
    (modify ?fact2
        (cf (combina-cf ?CF1 ?CF2))))

;; Macro categorie
;; Ogni fatto appartiene a una macro categoria
;; Ogni categoria pesa diversamente su disturbi diversi

(defrule anamnesi-patologica-remota
    (declare (salience ?*highest-priority*))
    (oav (object apr)(attribute $?)(value $?)(cf ?cf))
    =>
    (bind ?cf (* ?cf 0.1))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di pronuncia)(cf ?cf)))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di fluenza)(cf ?cf)))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di apprendimento)(cf ?cf)))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di voce)(cf ?cf)))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di deglutizione)(cf ?cf))))

(defrule prima-infanzia
    (declare (salience ?*highest-priority*))
    (oav (object prima infanzia)(attribute $?a)(value $?)(cf ?cf))
    =>
    (bind ?cf (* ?cf 0.15))
    (if (and (not (numberp (member$ gattonato ?a)))
        (not (numberp (member$ girello ?a)))
        (not (numberp (member$ cammina ?a)))
        (not (numberp (member$ pannolino ?a))))
    then (assert (oav (object diagnosi)(attribute esito)(value disturbo di pronuncia)(cf ?cf)))
        (assert (oav (object diagnosi)(attribute esito)(value disturbo di fluenza)(cf ?cf)))
        (assert (oav (object diagnosi)(attribute esito)(value disturbo di deglutizione)(cf ?cf))))
    ;;
    (if (or (numberp (member$ gattonato ?a))
        (numberp (member$ girello ?a))
        (numberp (member$ cammina ?a))
        (numberp (member$ pannolino ?a)))
    then (assert (oav (object diagnosi)(attribute esito)(value disturbo di apprendimento)(cf ?cf))))
    (if (eq ?a (create$ nei primi mesi aveva)) then
        (assert (oav (object diagnosi)(attribute esito)(value disturbo di voce)(cf ?cf)))))

(defrule malattie-infettive-contributo
    (declare (salience ?*highest-priority*))
    (oav (object malattie)(attribute infettive)(value $?)(cf ?cf))
    =>
    (bind ?cf (* ?cf 0.15))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di fluenza)(cf ?cf))))

(defrule altre-malattie-contributo
    (declare (salience ?*highest-priority*))
    (oav (object malattie)(attribute altre)(value $?)(cf ?cf))
    =>
    (bind ?cf (* ?cf 0.15))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di fluenza)(cf ?cf))))

(defrule affezioni-otorinolaringoiatriche-contributo
    (declare (salience ?*highest-priority*))
    (oav (object affezioni)(attribute otorinolaringoiatriche)(value $?)(cf ?cf))
    =>
    (bind ?cf (* ?cf 0.15))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di fluenza)(cf ?cf))))

(defrule linguaggio
    (declare (salience ?*highest-priority*))
    (oav (object linguaggio)(attribute $?)(value $?)(cf ?cf))
    =>
    (bind ?cf (* ?cf 0.15))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di pronuncia)(cf ?cf))))

(defrule socialita
    (declare (salience ?*highest-priority*))
    (oav (object socialita)(attribute $?)(value $?)(cf ?cf))
    =>
    (bind ?cf (* ?cf 0.15))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di pronuncia)(cf ?cf))))

(defrule studio
    (declare (salience ?*highest-priority*))
    (oav (object studio $?)(attribute $?)(value $?)(cf ?cf))
    =>
    (bind ?cf (* ?cf 0.15))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di apprendimento)(cf ?cf))))

(defrule difficolta
    (declare (salience ?*highest-priority*))
    (oav (object difficolta)(attribute di)(value $?)(cf ?cf))
    =>
    (bind ?cf (* ?cf 0.15))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di apprendimento)(cf ?cf))))

(defrule disfonia
    (declare (salience ?*highest-priority*))
    (oav (object disfonia)(attribute $?)(value $?)(cf ?cf))
    =>
    (bind ?cf (* ?cf 0.15))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di voce)(cf ?cf))))

;; disturbi

(defrule disturbo-di-pronuncia
    (declare (salience ?*highest-priority*))
    (oav (object visita)(attribute motivo)(value disturbo pronuncia)(cf ?cf1))
    (oav (object familiarita)(attribute comprende)(value ritardi di linguaggio)(cf ?cf2))
    =>
    (bind ?cf1 (* ?cf1 0.1))
    (bind ?cf2 (* ?cf2 0.25))
    (bind ?cf (/ (+ ?cf1 ?cf2) 2))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di pronuncia)(cf ?cf))))

(defrule disturbo-di-fluenza
    (declare (salience ?*highest-priority*))
    (oav (object visita)(attribute motivo)(value disturbo fluenza)(cf ?cf1))
    (oav (object familiarita)(attribute comprende)(value balbuzie)(cf ?cf2))
    =>
    (bind ?cf1 (* ?cf1 0.1))
    (bind ?cf2 (* ?cf2 0.25))
    (bind ?cf (/ (+ ?cf1 ?cf2) 2))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di fluenza)(cf ?cf))))

(defrule disturbo-di-apprendimento
    (declare (salience ?*highest-priority*))
    (oav (object visita)(attribute motivo)(value disturbo apprendimento)(cf ?cf1))
    (oav (object familiarita)(attribute comprende)(value disturbi di apprendimento)(cf ?cf2))
    =>
    (bind ?cf1 (* ?cf1 0.1))
    (bind ?cf2 (* ?cf2 0.25))
    (bind ?cf (/ (+ ?cf1 ?cf2) 2))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di apprendimento)(cf ?cf))))

(defrule disturbo-di-voce
    (declare (salience ?*highest-priority*))
    (oav (object visita)(attribute motivo)(value disturbo voce)(cf ?cf1))
    (oav (object familiarita)(attribute comprende)(value alterazioni di voce)(cf ?cf2))
    (oav (object familiarita)(attribute comprende)(value patologie vocali)(cf ?cf3))
    =>
    (bind ?cf1 (* ?cf1 0.1))
    (bind ?cf2 (* ?cf2 0.25))
    (bind ?cf3 (* ?cf3 0.25))
    (bind ?cf (/ (+ ?cf1 ?cf2 ?cf3) 3))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di voce)(cf ?cf))))

(defrule disturbo-di-deglutizione
    (declare (salience ?*highest-priority*))
    (oav (object visita)(attribute motivo)(value disturbo deglutizione)(cf ?cf1))
    (oav (object familiarita)(attribute comprende)(value turbe respiratorie rinolalie)(cf ?cf2))
    (oav (object familiarita)(attribute comprende)(value quadri sindromici malformazioni)(cf ?cf3))
    =>
    (bind ?cf1 (* ?cf1 0.1))
    (bind ?cf2 (* ?cf2 0.25))
    (bind ?cf3 (* ?cf3 0.25))
    (bind ?cf (/ (+ ?cf1 ?cf2 ?cf3) 3))
    (assert (oav (object diagnosi)(attribute esito)(value disturbo di deglutizione)(cf ?cf))))

;; test
(defrule test-linguaggio
    (oav (object diagnosi)(attribute esito)(value disturbo di pronuncia)(cf ?cf))
    (test (>= ?cf 0.5))
    =>
    (assert (oav (object test)(attribute consigliato)(value fonetico fonologico)(cf 1.0)))
    (assert (oav (object test)(attribute consigliato)(value lessicale semantico)(cf 1.0)))
    (assert (oav (object test)(attribute consigliato)(value morfosintattico)(cf 1.0)))
    (assert (oav (object test)(attribute consigliato)(value testuale)(cf 1.0))))

(defrule test-voce
    (declare (salience ?*low-priority*))
    (oav (object diagnosi)(attribute esito)(value disturbo di voce)(cf ?cf))
    (test (>= ?cf 0.5))
    =>
    (assert (oav (object test)(attribute consigliato)(value analisi qualitativa della voce)(cf 1.0))))

(defrule test-deglutizione
    (declare (salience ?*low-priority*))
    (oav (object diagnosi)(attribute esito)(value disturbo di deglutizione)(cf ?cf))
    (test (>= ?cf 0.5))
    =>
    (assert (oav (object test)(attribute consigliato)(value analisi morfologica e della muscolatura)(cf 1.0))))

;; esperti
(defrule logopedista
    (declare (salience ?*low-priority*))
    (oav (object diagnosi)(attribute esito)(value disturbo di pronuncia)(cf ?cf1))
    (oav (object diagnosi precedente)(attribute esperto)(value logopedista)(cf ?cf2))
    (test (>= ?cf1 0.5))
    (test (<= ?cf2 0.0))
    =>
    (assert (oav (object visita)(attribute consigliata)(value logopedista)(cf 1.0))))

(defrule neurologo
    (declare (salience ?*low-priority*))
    (oav (object diagnosi)(attribute esito)(value disturbo di fluenza)(cf ?cf1))
    (oav (object diagnosi precedente)(attribute esperto)(value neurologo)(cf ?cf2))
    (test (>= ?cf1 0.5))
    (test (<= ?cf2 0.0))
    =>
    (assert (oav (object visita)(attribute consigliata)(value neurologo)(cf 1.0))))

(defrule otorino
    (declare (salience ?*low-priority*))
    (oav (object diagnosi)(attribute esito)(value disturbo di voce)(cf ?cf1))
    (oav (object difficolta)(attribute di)(value udito)(cf ?cf2))
    (oav (object diagnosi precedente)(attribute esperto)(value otorino)(cf ?cf3))
    (test (>= ?cf1 0.5))
    (test (>= ?cf2 0.0))
    (test (<= ?cf3 0.0))
    =>
    (assert (oav (object visita)(attribute consigliata)(value otorino)(cf 1.0))))

(defrule odontoiatra
    (oav (object diagnosi)(attribute esito)(value disturbo di deglutizione)(cf ?cf))
    =>
    (if (< ?cf 0.5) then (assert (oav (object visita)(attribute consigliata)(value odontoiatra)(cf -1.0)))
    else (assert (oav (object visita)(attribute consigliata)(value odontoiatra)(cf 1.0)))))

(defrule oculista
    (oav (object difficolta)(attribute di)(value vista)(cf ?cf))
    (test (> ?cf 0.0))
    =>
    (assert (oav (object visita)(attribute consigliata)(value oculista)(cf 1.0))))

(defrule psicologo
    (oav (object difficolta)(attribute di)(value comportamento)(cf ?cf1))
    (oav (object difficolta)(attribute di)(value memoria)(cf ?cf2))
    (oav (object difficolta)(attribute di)(value aspetto socio-relazionale)(cf ?cf3))
    (oav (object difficolta)(attribute di)(value attenzione concentrazione)(cf ?cf4))
    (test (> (+ ?cf1 ?cf2 ?cf3 ?cf4) 2))
    =>
    (assert (oav (object visita)(attribute consigliata)(value psicologo)(cf 1.0))))

;; Esito anamnesi

(defrule esito-diagnosi-certo
    (declare (salience ?*low-priority*))
    (oav (object diagnosi)(attribute esito)(value $?disturbo)(cf ?cf1))
    (not (oav (object diagnosi)(attribute esito)(value $?disturbo)(cf ?cf2&:(neq ?cf1 ?cf2))))
    (not (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf3&:(> ?cf3 ?cf1))))
    (test (>= ?cf1 0.5))
    ?f <- (anamnesi (stato start))
    =>
    (modify ?f (stato stop))
    (printout t crlf "Sono emerse evidenze imputabili a " (implode$ ?disturbo) crlf))

(defrule esito-diagnosi-incerto
    (declare (salience ?*lowest-priority*))
    (not (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf&:(> ?cf 0.5))))
    ?f <- (anamnesi (stato start))
    =>
    (modify ?f (stato stop))
    (printout t crlf "Non ci sono abbastanza evidenze imputabili a disturbi o ritardi" crlf))

(defrule consiglia-test
    (oav (object test)(attribute consigliato)(value $?test)(cf ?cf1&:(> ?cf1 0.0)))
    (not (oav (object test)(attribute consigliato)(value $?test)(cf ?cf2&:(neq ?cf1 ?cf2))))
    (anamnesi (stato stop))
    =>
    (printout t crlf "Si consiglia la somministrazione di test " (implode$ ?test) crlf))

(defrule consiglia-visita
    (oav (object visita)(attribute consigliata)(value $?visita)(cf ?cf))
    (test (> ?cf 0.0))
    (anamnesi (stato stop))
    =>
    (printout t crlf "Per completezza diagnostica si consiglia visita a " (implode$ ?visita) crlf))

(defrule chiedi-di-fermarsi
    (declare (salience ?*lowest-priority*))
    ?f <- (anamnesi (stato ?a))
    =>
    (bind ?ris (ask-question "Continuare l'inferenza? " si no))
    (if (numberp (member$ si ?ris)) then (modify ?f (stato start))
    else (bind ?ris (ask-question "Resettare la working memory? " si no))
        (if (numberp (member$ si ?ris)) then (reset)
        else (return))))

;; Domande sonda

(defrule starting-rule
    (declare (salience (+ ?*highest-priority* 1)))
    =>
    (set-fact-duplication TRUE)
    (assert (anamnesi (stato start)))
    (printout t crlf crlf "*** Anamnesi del ritardo nello sviluppo del bambino ***" crlf crlf))

(defrule motivo
    (declare (salience ?*highest-priority*))
    (not (oav (object visita)(attribute motivo)(value $?)(cf ?)))
    (anamnesi (stato start))
    =>
    (printout t "Qual è il motivo del consulto?" crlf
        "1) Disturbo della pronuncia" crlf
        "2) Disturbo della fluenza (eg: balbuzie)" crlf
        "3) Disturbo di apprendimento" crlf
        "4) Disturbo di voce" crlf
        "5) Disturbo di deglutizione" crlf)
    (bind ?ris (ask-question "" 1 2 3 4 5))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object visita)(attribute motivo)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object visita)(attribute motivo)(value disturbo pronuncia)(cf 1.0)))
                else (assert (oav (object visita)(attribute motivo)(value disturbo pronuncia)(cf -1.0))))
            (if (numberp (member$ 2 ?ris)) then (assert (oav (object visita)(attribute motivo)(value disturbo fluenza)(cf 1.0)))
                else (assert (oav (object visita)(attribute motivo)(value disturbo fluenza)(cf -1.0))))
            (if (numberp (member$ 3 ?ris)) then (assert (oav (object visita)(attribute motivo)(value disturbo apprendimento)(cf 1.0)))
                else (assert (oav (object visita)(attribute motivo)(value disturbo apprendimento)(cf -1.0))))
            (if (numberp (member$ 4 ?ris)) then (assert (oav (object visita)(attribute motivo)(value disturbo voce)(cf 1.0)))
                else (assert (oav (object visita)(attribute motivo)(value disturbo voce)(cf -1.0))))
            (if (numberp (member$ 5 ?ris)) then (assert (oav (object visita)(attribute motivo)(value disturbo deglutizione)(cf 1.0)))
                else (assert (oav (object visita)(attribute motivo)(value disturbo deglutizione)(cf -1.0))))))

;; domande di familiarità

(defrule familiarita
    (declare (salience ?*high-priority*))
    (not (oav (object familiarita)(attribute comprende)(value $?)(cf ?)))
    (anamnesi (stato start))
    =>
    (printout t "In famiglia, (considerando anche nonni, zii, cugini, ecc.) ")
    (printout t "sono o sono stati presenti casi di:" crlf)
    (printout t "1) Ritardi di linguaggio?" crlf "2) Balbuzie o disfluenze?" crlf
        "3) Ipoacusia o sordità?" crlf "4) Alterazioni di voce?" crlf
        "5) Disturbi di apprendimento?" crlf "6) Malattie nervose o psichiche?" crlf
        "7) Turbe respiratorie o rinolalie?" crlf "8) Quadri sindromici o malformazioni?" crlf)
    (bind ?ris (ask-question "" 1 2 3 4 5 6 7 8 no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object familiarita)(attribute comprende)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object familiarita)(attribute comprende)(value ritardi di linguaggio)(cf 1.0)))
            else (assert (oav (object familiarita)(attribute comprende)(value ritardi di linguaggio)(cf -1.0))))
            (if (numberp (member$ 2 ?ris)) then (assert (oav (object familiarita)(attribute comprende)(value balbuzie disfluenze)(cf 1.0)))
                else (assert (oav (object familiarita)(attribute comprende)(value balbuzie disfluenze)(cf -1.0))))
            (if (numberp (member$ 3 ?ris)) then (assert (oav (object familiarita)(attribute comprende)(value ipoacusia sordita)(cf 1.0)))
                else (assert (oav (object familiarita)(attribute comprende)(value ipoacusia sordita)(cf -1.0))))
            (if (numberp (member$ 4 ?ris)) then (assert (oav (object familiarita)(attribute comprende)(value alterazioni voce)(cf 1.0)))
                else (assert (oav (object familiarita)(attribute comprende)(value alterazioni voce)(cf -1.0))))
            (if (numberp (member$ 5 ?ris)) then (assert (oav (object familiarita)(attribute comprende)(value disturbi di apprendimento)(cf 1.0)))
                else (assert (oav (object familiarita)(attribute comprende)(value disturbi di apprendimento)(cf -1.0))))
            (if (numberp (member$ 6 ?ris)) then (assert (oav (object familiarita)(attribute comprende)(value malattie nervose psichiche)(cf 1.0)))
                else (assert (oav (object familiarita)(attribute comprende)(value malattie nervose psichiche)(cf -1.0))))
            (if (numberp (member$ 7 ?ris)) then (assert (oav (object familiarita)(attribute comprende)(value turbe respiratorie rinolalie)(cf 1.0)))
                else (assert (oav (object familiarita)(attribute comprende)(value turbe respiratorie rinolalie)(cf -1.0))))
            (if (numberp (member$ 8 ?ris)) then (assert (oav (object familiarita)(attribute comprende)(value quadri sindromici malformazioni)(cf 1.0)))
                else (assert (oav (object familiarita)(attribute comprende)(value quadri sindromici malformazioni)(cf -1.0))))))

(defrule diagnosi-precedente
    (declare (salience ?*high-priority*))
    (not (oav (object diagnosi precedente)(attribute esperto)(value $?)(cf ?)))
    (anamnesi (stato start))
    =>
    (bind ?ris (ask-question "Il bambino ha già diagnosi? " "" si no))
    (if (numberp (member$ ns ?ris)) then
            (assert (oav (object diagnosi precedente)(attribute esperto)(value incerto)(cf 0.0)))
        else (if (numberp (member$ no ?ris)) then
            (assert (oav (object diagnosi precedente)(attribute esperto)(value foniatra)(cf -1.0)))
            (assert (oav (object diagnosi precedente)(attribute esperto)(value otorino)(cf -1.0)))
            (assert (oav (object diagnosi precedente)(attribute esperto)(value neuropsichiatra infantile)(cf -1.0)))
            (assert (oav (object diagnosi precedente)(attribute esperto)(value neurologo)(cf -1.0)))
            else (printout t "Da chi?" crlf
                "1) Foniatra" crlf "2) Otorino" crlf
                "3) Neuropsichiatra infantile" crlf "4) Neurologo" crlf
                "5) Altro" crlf)
            (bind ?ris (ask-question "" 1 2 3 4 5))
            (if (numberp (member$ ns ?ris))
                then
                    (assert (oav (object diagnosi precedente)(attribute esperto)(value incerto)(cf 0.0)))
                else (if (numberp (member$ 1 ?ris)) then (assert (oav (object diagnosi precedente)(attribute esperto)(value foniatra)(cf 1.0)))
                        else (assert (oav (object diagnosi precedente)(attribute esperto)(value foniatra)(cf -1.0))))
                    (if (numberp (member$ 2 ?ris)) then (assert (oav (object diagnosi precedente)(attribute esperto)(value otorino)(cf 1.0)))
                        else (assert (oav (object diagnosi precedente)(attribute esperto)(value otorino)(cf -1.0))))
                    (if (numberp (member$ 3 ?ris)) then (assert (oav (object diagnosi precedente)(attribute esperto)(value neuropsichiatra infantile)(cf 1.0)))
                        else (assert (oav (object diagnosi precedente)(attribute esperto)(value neuropsichiatra infantile)(cf -1.0))))
                    (if (numberp (member$ 4 ?ris)) then (assert (oav (object diagnosi precedente)(attribute esperto)(value neurologo)(cf 1.0)))
                        else (assert (oav (object diagnosi precedente)(attribute esperto)(value neurologo)(cf -1.0))))
                    (if (numberp (member$ 5 ?ris)) then (printout t " >> ")
                        (assert (oav (object diagnosi precedente)(attribute esperto)(value (explode$ (lowcase (readline))))(cf 1.0))))))))

;; Analisi Patologica Remota

(defrule complicazioni-in-gravidanza
    (not (oav (object apr)(attribute complicazioni gravidanza)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (bind ?ris (ask-question "Ci sono state complicanze durante il parto?" "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object apr)(attribute complicazioni gravidanza)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris))
            then (assert (oav (object apr)(attribute complicazioni gravidanza)(value si)(cf 0.3)))
            else (assert (oav (object apr)(attribute complicazioni gravidanza)(value no)(cf -0.3))))))

(defrule malattie-in-gravidanza
    (oav (object apr)(attribute complicazioni gravidanza)(value si)(cf ?))
    (not (oav (object apr)(attribute malattie gravidanza)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (bind ?ris (ask-question "Si sono avute malattie durante il parto?" "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object apr)(attribute malattie gravidanza)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris))
            then (assert (oav (object apr)(attribute malattie gravidanza)(value si)(cf 0.3)))
            else (assert (oav (object apr)(attribute malattie gravidanza)(value si)(cf -0.3))))))

(defrule malattie-in-gravidanza-quali
    (oav (object apr)(attribute malattie gravidanza)(value si)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object apr)(attribute malattia gravidanza)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Quali malattie si sono avute durante il parto?" crlf)
    (printout t "1) Complesso TORCH" crlf)
    (printout t "2) Diabete" crlf)
    (printout t "3) Disturbi Circolatori" crlf)
    (printout t "4) Malattie Endocrine" crlf)
    (printout t "5) Eclampsia o Pre-Eclampsia" crlf)
    (printout t "6) Emorragie o minacce d'aborto" crlf)
    (printout t "7) Altro" crlf)
    (bind ?ris (ask-question "(È possibile indicare più risposte oppure digitare NO)"
        "Il complesso TORCH include toxoplasmosi, rosolia, citomegalovirus ed herpes simplex" 1 2 3 4 5 6 7 no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object apr)(attribute malattia gravidanza)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris))
            then (assert (oav (object apr)(attribute malattia gravidanza)(value complesso torch)(cf 1.0)))
            else (assert (oav (object apr)(attribute malattia gravidanza)(value complesso torch)(cf -0.1))))
        (if (numberp (member$ 2 ?ris))
            then (assert (oav (object apr)(attribute malattia gravidanza)(value diabete)(cf 1.0)))
            else (assert (oav (object apr)(attribute malattia gravidanza)(value diabete)(cf -0.1))))
        (if (numberp (member$ 3 ?ris))
            then (assert (oav (object apr)(attribute malattia gravidanza)(value disturbi circolatori)(cf 1.0)))
            else (assert (oav (object apr)(attribute malattia gravidanza)(value disturbi circolatori)(cf -0.1))))
        (if (numberp (member$ 4 ?ris))
            then (assert (oav (object apr)(attribute malattia gravidanza)(value malattie endocrine)(cf 1.0)))
            else (assert (oav (object apr)(attribute malattia gravidanza)(value malattie endocrine)(cf -0.1))))
        (if (numberp (member$ 5 ?ris))
            then (assert (oav (object apr)(attribute malattia gravidanza)(value eclampsia)(cf 1.0)))
            else (assert (oav (object apr)(attribute malattia gravidanza)(value eclampsia)(cf -0.1))))
        (if (numberp (member$ 6 ?ris))
            then (assert (oav (object apr)(attribute malattia gravidanza)(value emorragie)(cf 1.0)))
            else (assert (oav (object apr)(attribute malattia gravidanza)(value emorragie)(cf -0.1))))))

(defrule farmaci-in-gravidanza
    (oav (object apr)(attribute complicazioni gravidanza)(value si)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object apr)(attribute farmaci gravidanza)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "La madre ha fatto uso di farmaci durante la gravidanza?")
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object apr)(attribute farmaci gravidanza)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris))
            then (assert (oav (object apr)(attribute farmaci gravidanza)(value si)(cf 1.0)))
            else (assert (oav (object apr)(attribute farmaci gravidanza)(value no)(cf -0.1))))))

(defrule alcool-in-gravidanza
    (oav (object apr)(attribute complicazioni gravidanza)(value si)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object apr)(attribute alcool gravidanza)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "La madre ha fatto uso di alcool durante la gravidanza?")
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object apr)(attribute alcool gravidanza)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris))
            then (assert (oav (object apr)(attribute alcool gravidanza)(value si)(cf 1.0)))
            else (assert (oav (object apr)(attribute alcool gravidanza)(value no)(cf -0.1))))))

(defrule fumo-in-gravidanza
    (oav (object apr)(attribute complicazioni gravidanza)(value si)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object apr)(attribute fumo gravidanza)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "La madre ha fumato durante la gravidanza?")
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object apr)(attribute fumo gravidanza)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris))
            then (assert (oav (object apr)(attribute fumo gravidanza)(value si)(cf 0.1)))
            else (assert (oav (object apr)(attribute fumo gravidanza)(value si)(cf -0.1))))))

(defrule sigarette-in-gravidanza
    (oav (object apr)(attribute fumo gravidanza)(value si)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object apr)(attribute sigarette gravidanza)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "In media, si sono consumate più di dieci sigarette al giorno?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object apr)(attribute sigarette gravidanza)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris))
            then (assert (oav (object apr)(attribute sigarette gravidanza)(value piu di dieci)(cf 1.0)))
            else (assert (oav (object apr)(attribute sigarette gravidanza)(value piu di dieci)(cf -0.1))))))

(defrule nato-a-termine
    (oav (object apr)(attribute complicazioni gravidanza)(value si)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object apr)(attribute termine gravidanza)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino è nato a termine?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object apr)(attribute termine gravidanza)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris))
            then (assert (oav (object apr)(attribute termine gravidanza)(value si)(cf -0.1)))
            else (assert (oav (object apr)(attribute termine gravidanza)(value no)(cf 0.1))))))

(defrule pre-termine-o-post-termine
    (oav (object apr)(attribute termine gravidanza)(value no)(cf ?))
    (not (oav (object apr)(attribute termine gravidanza)(value pre)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino è nato:" crlf
        "1) Pre-termine" crlf "2) Post-materno" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object apr)(attribute termine gravidanza)(value incerto)(cf 0.0)))
        else (assert (oav (object apr)(attribute termine gravidanza)(value pre)(cf 1.0)))))

(defrule tipo-di-parto
    (oav (object apr)(attribute complicazioni gravidanza)(value $?)(cf ?))
    (not (oav (object apr)(attribute tipo gravidanza)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il parto è stato:" crlf "1) Naturale;" crlf "2) Cesareo;" crlf )
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object apr)(attribute tipo gravidanza)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object apr)(attribute tipo gravidanza)(value naturale)(cf -0.1)))
            else (assert (oav (object apr)(attribute tipo gravidanza)(value cesareo)(cf 1.0))))))

(defrule motivazione-cesareo
    (oav (object apr)(attribute tipo gravidanza)(value cesareo)(cf ?c1))
    (test (< ?c1 0.0))
    (not (oav (object apr)(attribute motivazione cesareo)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Indicare la motivazione del parto cesareo:" crlf
        "1) Posizione anomala;" crlf
        "2) Cordone ombelicale intorno al collo;" crlf
        "3) Sofferenza fatale;" crlf
        "4) Altro")
    (bind ?ris (ask-question "" 1 2 3 4))
    (if (numberp (member$ ns ?ris)) then
            (assert (oav (object apr)(attribute motivazione cesareo)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then
                (assert (oav (object apr)(attribute motivazione cesareo)(value posizione anomala)(cf 1.0))))
            (if (numberp (member$ 2 ?ris)) then
                (assert (oav (object apr)(attribute motivazione cesareo)(value cordone intorno al collo)(cf 1.0))))
            (if (numberp (member$ 3 ?ris)) then
                (assert (oav (object apr)(attribute motivazione cesareo)(value sofferenza fatale)(cf 1.0))))
            (if (numberp (member$ 4 ?ris)) then
                (assert (oav (object apr)(attribute motivazione cesareo)(value altro)(cf 1.0))))))

(defrule durata-parto
    (not (oav (object apr)(attribute durata gravidanza)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il parto è durato:" crlf
        "1) Meno di 24 ore" crlf "2) Da 24 ore in su" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object apr)(attribute durata gravidanza)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then (assert (oav (object apr)(attribute durata gravidanza)(value piu di ventiquattro ore)(cf -0.1)))
         else (assert (oav (object apr)(attribute durata gravidanza)(value piu di ventiquattro ore)(cf 1.0))))))

(defrule pianto
    (not (oav (object apr)(attribute neonato ha pianto)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Appena nato il bambino ha pianto subito?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object apr)(attribute neonato ha pianto)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris))
            then (assert (oav (object apr)(attribute neonato ha pianto)(value non subito)(cf -0.1)))
            else (assert (oav (object apr)(attribute neonato ha pianto)(value non subito)(cf 1.0))))))

(defrule ittero
    (not (oav (object apr)(attribute neonato ha avuto)(value ittero $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Appena nato il bambino ha avuto ittero?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object apr)(attribute neonato ha avuto)(value ittero incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object apr)(attribute neonato ha avuto)(value ittero)(cf 1.0)))
            else (assert (oav (object apr)(attribute neonato ha avuto)(value ittero)(cf -0.1))))))

(defrule durata-ittero
    (oav (object apr)(attribute neonato ha avuto)(value ittero)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object apr)(attribute durata ittero)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Per quanto tempo da neonato ha avuto ittero?" crlf
        "1) Meno di una settimana" crlf "2) Più di una settimana" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object apr)(attribute durata ittero)(value ittero incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object apr)(attribute durata ittero)(value piu di una settimana)(cf -0.1)))
            else (assert (oav (object apr)(attribute durata ittero)(value piu di una settimana)(cf 1.0))))))

(defrule cianosi
    (not (oav (object apr)(attribute neonato ha avuto)(value cianosi $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Appena nato il bambino ha avuto cianosi?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object apr)(attribute neonato ha avuto)(value cianosi incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object apr)(attribute neonato ha avuto)(value cianosi)(cf 1.0)))
            else (assert (oav (object apr)(attribute neonato ha avuto)(value cianosi)(cf -0.1))))))

(defrule durata-cianosi
    (oav (object apr)(attribute neonato ha avuto)(value cianosi)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object apr)(attribute durata cianosi)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Per quanto tempo da neonato ha avuto cianosi?" crlf
        "1) Meno di una settimana" crlf "2) Più di una settimana" crlf )
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object apr)(attribute durata cianosi)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object apr)(attribute durata cianosi)(value piu di una settimana)(cf -0.1)))
            else (assert (oav (object apr)(attribute durata cianosi)(value piu di una settimana)(cf 1.0))))))

(defrule incubatrice
    (not (oav (object apr)(attribute neonato ha usato)(value incubatrice $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Appena nato il bambino ha avuto bisogno dell'incubatrice?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object apr)(attribute neonato ha usato)(value incubatrice incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object apr)(attribute neonato ha usato)(value incubatrice)(cf 1.0)))
            else (assert (oav (object apr)(attribute neonato ha usato)(value incubatrice)(cf -0.1))))))

(defrule durata-incubatrice
    (oav (object apr)(attribute neonato ha usato)(value incubatrice)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object apr)(attribute durata incubatrice)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Per quanto tempo è rimasto nell'incubatrice?" crlf
        "1) Meno di una settimana" crlf "2) Più di una settimana" crlf )
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object apr)(attribute durata incubatrice)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object apr)(attribute durata incubatrice)(value piu di una settimana)(cf -0.1)))
            else (assert (oav (object apr)(attribute durata incubatrice)(value piu di una settimana)(cf 1.0))))))

(defrule malformazioni
    (not (oav (object apr)(attribute neonato ha avuto)(value malformazioni $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Appena nato il bambino aveva delle malformazioni al viso?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object apr)(attribute neonato ha avuto)(value malformazioni incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object apr)(attribute neonato ha avuto)(value malformazioni)(cf 1.0)))
            else (assert (oav (object apr)(attribute neonato ha avuto)(value malformazioni)(cf -0.1))))))

(defrule punteggio-apgar
    (not (oav (object apr)(attribute punteggio apgar)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il punteggio APGAR del bambino alla nascita era:" crlf
        "1) Inferiore a 4" crlf
        "2) Tra 4 e 6" crlf
        "3) Tra 7 e 10")
    (bind ?ris (ask-question "" 1 2 3))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object apr)(attribute punteggio apgar)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then
        (assert (oav (object apr)(attribute punteggio apgar)(value meno di quattro)(cf 1.0)))
        else (if (numberp (member$ 2 ?ris)) then
            (assert (oav (object apr)(attribute punteggio apgar)(value tra quattro e sei)(cf 0.5)))
            else (if (numberp (member$ 3 ?ris)) then
                (assert (oav (object apr)(attribute punteggio apgar)(value tra sette e dieci)(cf -1.0))))))))

;; Prima Infanzia

(defrule allattamento-materno
    (not (oav (object prima infanzia)(attribute allattamento materno)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Da neonato ha ricevuto allattamento materno?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute allattamento materno)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object prima infanzia)(attribute allattamento materno)(value ricevuto)(cf 0.1)))
            else (assert (oav (object prima infanzia)(attribute allattamento materno)(value ricevuto)(cf -0.1))))))

(defrule allattamento-materno-durata
    (oav (object prima infanzia)(attribute allattamento materno)(value ricevuto)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object prima infanzia)(attribute durata allattamento materno)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Per quanto tempo ha ricevuto allattamento materno?" crlf
        "1) Fino a 6 mesi" crlf "2) Fino a 12 mesi" crlf "3) Fino a 18 mesi" crlf
        "4) Fino a 24 mesi" crlf "5) Oltre 24 mesi" crlf)
    (bind ?ris (ask-question "" 1 2 3 4 5))
        (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute durata allattamento materno)(value incerto)(cf 0.0)))
            else (if (numberp (member$ 5 ?ris)) then (assert (oav (object prima infanzia)(attribute durata allattamento materno)(value oltre ventiquattro mesi)(cf 1.0)))
                    else (assert (oav (object prima infanzia)(attribute durata allattamento materno)(value non oltre ventiquattro mesi)(cf -0.1))))))

(defrule motivo-mancato-allattamento
    (oav (object prima infanzia)(attribute allattamento materno)(value ricevuto)(cf ?c1))
    (test (< ?c1 0.0))
    (not (oav (object prima infanzia)(attribute motivo mancato allattamento materno)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Indicare il motivo per cui non ha ricevuto allattamento materno:" crlf
        "1) Mancata montata lattea" crlf
        "2) Difficoltà di suzione" crlf
        "3) Altro" crlf)
    (bind ?ris (ask-question "" 1 2 3))
    (if (numberp (member$ ns ?ris)) then
        (assert (oav (object prima infanzia)(attribute motivo mancato allattamento materno)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 2 ?ris)) then
            (assert (oav (object prima infanzia)(attribute motivo mancato allattamento materno)(value difficolta di suzione)(cf 1.0)))
            else (assert (oav (object prima infanzia)(attribute motivo mancato allattamento materno)(value altro)(cf -0.1))))))

(defrule allattamento-artificiale
    (not (oav (object prima infanzia)(attribute allattamento artificiale)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Da neonato ha ricevuto allattamento artificiale?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute allattamento artificiale)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object prima infanzia)(attribute allattamento artificiale)(value ricevuto)(cf 0.1)))
            else (assert (oav (object prima infanzia)(attribute allattamento artificiale)(value non ricevuto)(cf -0.1))))))

(defrule allattamento-artificiale-durata
    (oav (object prima infanzia)(attribute allattamento artificiale)(value ricevuto)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object prima infanzia)(attribute durata allattamento artificiale)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Per quanto tempo ha ricevuto allattamento artificiale?" crlf
        "1) Fino a 3 mesi" crlf "2) Fino a 6 mesi" crlf "3) Fino a 12 mesi" crlf "4) Fino a 18 mesi" crlf
        "5) Fino a 24 mesi" crlf "6) Oltre 24 mesi" crlf)
    (bind ?ris (ask-question "" 1 2 3 4 5 6))
    (if (numberp (member$ ns ?ris)) then
        (assert (oav (object prima infanzia)(attribute durata allattamento artificiale)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 6 ?ris)) then (assert (oav (object prima infanzia)(attribute durata allattamento artificiale)(value oltre ventiquattro mesi)(cf 1.0)))
            else (assert (oav (object prima infanzia)(attribute durata allattamento artificiale)(value non oltre ventiquattro mesi)(cf -0.1))))))

(defrule mangiava-nei-primi-mesi
    (not (oav (object prima infanzia)(attribute nei primi mesi mangiava)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Nei primi mesi, il bambino mangiava:" crlf
        "1) Regolarmente" crlf "2) Spesso" crlf "3) Poco" crlf)
    (bind ?ris (ask-question "" 1 2 3))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute nei primi mesi mangiava)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 3 ?ris)) then (assert (oav (object prima infanzia)(attribute nei primi mesi mangiava)(value poco)(cf 1.0)))
        else (assert (oav (object prima infanzia)(attribute nei primi mesi mangiava)(value non poco)(cf -0.1))))))

(defrule mangiava-poco-motivo
    (oav (object prima infanzia)(attribute nei primi mesi mangiava)(value poco)(cf ?cf1))
    (test (> ?cf1 0.0))
    (not (oav (object prima infanzia)(attribute mangiava poco perche)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Indicare le motivazioni per cui il bambino mangiava poco nei primi mesi di vita:" crlf
        "1) Difficoltà di suzione o alimentari" crlf
        "2) Scarso appetito" crlf "3) Altro" crlf )
    (bind ?ris (ask-question "" 1 2 3))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute mangiava poco perche)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then (assert (oav (object prima infanzia)(attribute mangiava poco perche)(value difficolta di suzione)(cf 1.0)))
        else (assert (oav (object prima infanzia)(attribute mangiava poco perche)(value altro)(cf -0.1))))))

(defrule aveva-nei-primi-mesi
    (not (oav (object prima infanzia)(attribute nei primi mesi aveva)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Nei primi mesi, il bambino aveva:" crlf
        "1) Frequenti disturbi instestinali" crlf "2) Vomiti frequenti" crlf
        "3) Calo di peso" crlf "4) Reflusso gastro-esofageo" crlf)
    (printout t "(è possibile indicare più risposte oppure digitare NO)")
    (bind ?ris (ask-question "" 1 2 3 4 no))
    (if (numberp (member$ ns ?ris)) then
        (assert (oav (object prima infanzia)(attribute nei primi mesi aveva)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object prima infanzia)(attribute nei primi mesi aveva)(value frequenti disturbi intestinali)(cf 1.0)))
            else (assert (oav (object prima infanzia)(attribute nei primi mesi aveva)(value frequenti disturbi intestinali)(cf -0.1))))
        (if (numberp (member$ 2 ?ris)) then (assert (oav (object prima infanzia)(attribute nei primi mesi aveva)(value frequenti vomiti frequenti)(cf 1.0)))
            else (assert (oav (object prima infanzia)(attribute nei primi mesi aveva)(value frequenti vomiti frequenti)(cf -0.1))))
        (if (numberp (member$ 3 ?ris)) then (assert (oav (object prima infanzia)(attribute nei primi mesi aveva)(value frequenti calo di peso)(cf 1.0)))
            else (assert (oav (object prima infanzia)(attribute nei primi mesi aveva)(value frequenti calo di peso)(cf -0.1))))
        (if (numberp (member$ 4 ?ris)) then (assert (oav (object prima infanzia)(attribute nei primi mesi aveva)(value frequenti reflusso gastro-esofageo)(cf 1.0)))
            else (assert (oav (object prima infanzia)(attribute nei primi mesi aveva)(value frequenti reflusso gastro-esofageo)(cf -0.1))))))

(defrule perdeva-bava
    (not (oav (object prima infanzia)(attribute nei primi mesi perdeva bava)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Nei primi mesi, il bambino perdeva bava dalla bocca:" crlf
        "1) Mai" crlf "2) Talvolta" crlf "3) Spesso" crlf)
    (bind ?ris (ask-question "" 1 2 3))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute nei primi mesi perdeva bava)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 3 ?ris)) then (assert (oav (object prima infanzia)(attribute nei primi mesi perdeva bava)(value spesso)(cf 1.0)))
        else (assert (oav (object prima infanzia)(attribute nei primi mesi perdeva bava)(value spesso)(cf -0.1))))))

(defrule come-mastica
    (not (oav (object prima infanzia)(attribute mastica come)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Come mastica il bambino?" crlf
        "1) Lentamente e a bocca aperta" crlf "2) Lentamente e a bocca chiusa" crlf
        "3) Normalmente" crlf "4) Velocemente quasi senza masticare" crlf)
    (bind ?ris (ask-question "" 1 2 3 4))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute mastica come)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 3 ?ris)) then (assert (oav (object prima infanzia)(attribute mastica come)(value normalmente)(cf -0.1)))
        else (assert (oav (object prima infanzia)(attribute mastica come)(value anomalo)(cf 1.0))))))

(defrule cosa-mastica
    (not (oav (object prima infanzia)(attribute mastica cosa)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Ad oggi il bambino mastica consistenze:" crlf
        "1) Varie" crlf "2) Principalmente semisolide" crlf
        "3) Principalmente semiliquide" crlf "4) Evita alimenti filanti" crlf
        "5) Evita alimenti particolarmente solidi" crlf)
    (bind ?ris (ask-question "" 1 2 3 4 5))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute mastica cosa)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then (assert (oav (object prima infanzia)(attribute mastica cosa)(value varie)(cf -0.1)))
        else (assert (oav (object prima infanzia)(attribute mastica cosa)(value consistenze specifiche)(cf 1.0))))))

(defrule ha-usato-ciuccio
    (not (oav (object ciuccio)(attribute ha usato)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino ha fatto uso di ciuccio?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object ciuccio)(attribute ha usato)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object ciuccio)(attribute ha usato)(value si)(cf 1.0)))
            else (assert (oav (object ciuccio)(attribute ha usato)(value no)(cf -0.1))))))

(defrule eta-ciuccio
    (oav (object ciuccio)(attribute ha usato)(value si)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object prima infanzia)(attribute ciuccio fino a)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Fino a che età a usato il ciuccio?" crlf)
    (printout t "1) Meno di 4 anni" crlf "2) Più di 4 anni" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute ciuccio fino a)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object prima infanzia)(attribute ciuccio fino a)(value piu di quattro anni)(cf 1.0)))
            else (assert (oav (object prima infanzia)(attribute ciuccio fino a)(value piu di quattro anni)(cf -0.1))))))

(defrule frequenza-ciuccio
    (oav (object ciuccio)(attribute ha usato)(value si)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object prima infanzia)(attribute ciuccio quando)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Quando ha usato il ciuccio?" crlf)
    (printout t "1) Sempre" crlf "2) Solo per addormentarsi" crlf )
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute ciuccio quando)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object prima infanzia)(attribute ciuccio quando)(value sempre)(cf 1.0)))
            else (assert (oav (object prima infanzia)(attribute ciuccio quando)(value sempre)(cf -0.1))))))

(defrule ha-usato-biberon
    (not (oav (object biberon)(attribute ha usato)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino ha fatto uso di biberon?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object biberon)(attribute ha usato)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object biberon)(attribute ha usato)(value si)(cf 1.0)))
            else (assert (oav (object biberon)(attribute ha usato)(value no)(cf -0.1))))))

(defrule eta-biberon
    (oav (object biberon)(attribute ha usato)(value si)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object prima infanzia)(attribute biberon fino a)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Fino a che età a usato il biberon?" crlf)
    (printout t "1) Meno di 4 anni" crlf "2) Più di 4 anni" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute biberon fino a)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object prima infanzia)(attribute biberon fino a)(value meno di quattro anni)(cf -0.1)))
            else (assert (oav (object prima infanzia)(attribute biberon fino a)(value piu di quattro anni)(cf 1.0))))))

(defrule frequenza-biberon
    (oav (object biberon)(attribute ha usato)(value si)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object prima infanzia)(attribute biberon quando)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Quando ha usato il biberon?" crlf)
    (printout t "1) Solo la mattina" crlf "2) Spesso durante la giornata" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute biberon quando)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object prima infanzia)(attribute biberon quando)(value solo la mattina)(cf -0.1)))
            else (assert (oav (object prima infanzia)(attribute biberon quando)(value spesso durante la giornata)(cf 1.0))))))

(defrule succhia-il-dito
    (not (oav (object prima infanzia)(attribute dito succhia)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino si succhia il dito?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute dito succhia)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object prima infanzia)(attribute dito succhia)(value si)(cf 1.0)))
            else (assert (oav (object prima infanzia)(attribute dito succhia)(value si)(cf -0.1))))))

(defrule succhia-il-dito-eta
    (oav (object prima infanzia)(attribute dito succhia)(value si)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object prima infanzia)(attribute dito fino a)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Fino a che età si è succhiato il dito?" crlf)
    (printout t "1) Meno di 4 anni" crlf "2) Più di 4 anni" crlf )
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute dito fino a)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object prima infanzia)(attribute dito fino a)(value meno di quattro anni)(cf -0.1)))
            else (assert (oav (object prima infanzia)(attribute dito fino a)(value piu di quattro anni)(cf 1.0))))))

(defrule ha-usato-il-girello
    (not (oav (object prima infanzia)(attribute girello ha usato)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino ha usato il girello?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute girello ha usato)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object prima infanzia)(attribute girello ha usato)(value si)(cf 1.0)))
            else (assert (oav (object prima infanzia)(attribute girello ha usato)(value si)(cf -0.1))))))

(defrule camminare-da-solo-eta
    (not (oav (object prima infanzia)(attribute cammina da solo da)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "A che età ha iniziato a camminare da solo?" crlf)
    (printout t "1) Meno di 12 mesi" crlf "2) Tra 12 e 18 mesi" crlf
        "3) Più di 18 mesi" crlf )
    (bind ?ris (ask-question "" 1 2 3))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute cammina da solo da)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 3 ?ris)) then (assert (oav (object prima infanzia)(attribute cammina da solo da)(value piu di diciotto mesi)(cf 1.0)))
        else (assert (oav (object prima infanzia)(attribute cammina da solo da)(value meno di diciotto mesi)(cf -0.1))))))

(defrule pannolino-eta
    (not (oav (object prima infanzia)(attribute pannolino tolto a)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "A che età ha tolto il pannolino?" crlf)
    (printout t "1) 18 mesi" crlf "2) 24  mesi" crlf
        "3) 36 mesi" crlf "4) Ne continua a fare uso tuttora" crlf )
    (bind ?ris (ask-question "" 1 2 3 4))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object prima infanzia)(attribute pannolino tolto a)(value incerto)(cf 0.0)))
    else (if (or (numberp (member$ 3 ?ris))(numberp (member$ 4 ?ris))) then
        (assert (oav (object prima infanzia)(attribute pannolino tolto a)(value trentasei mesi)(cf 1.0)))
        else (assert (oav (object prima infanzia)(attribute pannolino tolto a)(value meno di trentasei mesi)(cf -0.1))))))

(defrule vaccino-ricevuto
    (not (oav (object vaccino)(attribute ricevuto)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino è stato vaccinato?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object vaccino)(attribute ricevuto)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object vaccino)(attribute ricevuto)(value si)(cf 0.05)))
            else (assert (oav (object vaccino)(attribute ricevuto)(value si)(cf -0.05))))))

(defrule vaccino-complicazioni
    (oav (object vaccino)(attribute ricevuto)(value si)(cf ?c1))
    (not (oav (object vaccino)(attribute complicazioni)(value $?)(cf ?c1)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Sono sorte complicazioni dal vaccino?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object vaccino)(attribute complicazioni)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object vaccino)(attribute complicazioni)(value si)(cf 1.0)))
            else (assert (oav (object vaccino)(attribute complicazioni)(value no)(cf -0.1))))))

;; FLUENZA

(defrule malattie-infettive
    (not (oav (object malattie)(attribute infettive)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino ha avuto alcuna delle seguenti malattie?" crlf
        "1) Morbillo" crlf "2) Rosolia" crlf "3) Scarlattina" crlf
        "4) Parotite" crlf "5) Varicella" crlf "6) Difterite" crlf
        "7) Quarta malattia" crlf "8) Orecchioni" crlf "9) Pertosse" crlf)
    (printout t "(Indicare i numeri corrispondenti separandoli con uno spazio o digitare NO)" crlf)
    (bind ?ris (ask-question "" 1 2 3 4 5 6 7 8 9 no))
    (if (numberp (member$ ns ?ris)) then
            (assert (oav (object malattie)(attribute infettive)(value incerto)(cf 0.0)))
        else
            (if (numberp (member$ 1 ?ris)) then (assert (oav (object malattie)(attribute infettive)(value morbillo)(cf 1.0)))
                else (assert (oav (object malattie)(attribute infettive)(value morbillo)(cf -0.1))))
            (if (numberp (member$ 2 ?ris)) then (assert (oav (object malattie)(attribute infettive)(value rosolia)(cf 1.0)))
                else (assert (oav (object malattie)(attribute infettive)(value rosolia)(cf -0.1))))
            (if (numberp (member$ 3 ?ris)) then (assert (oav (object malattie)(attribute infettive)(value scarlattina)(cf 1.0)))
                else (assert (oav (object malattie)(attribute infettive)(value scarlattina)(cf -0.1))))
            (if (numberp (member$ 4 ?ris)) then (assert (oav (object malattie)(attribute infettive)(value parotite)(cf 1.0)))
                else (assert (oav (object malattie)(attribute infettive)(value parotite)(cf -0.1))))
            (if (numberp (member$ 5 ?ris)) then (assert (oav (object malattie)(attribute infettive)(value varicella)(cf 1.0)))
                else (assert (oav (object malattie)(attribute infettive)(value varicella)(cf -0.1))))
            (if (numberp (member$ 6 ?ris)) then (assert (oav (object malattie)(attribute infettive)(value difterite)(cf 1.0)))
                else (assert (oav (object malattie)(attribute infettive)(value difterite)(cf -0.1))))
            (if (numberp (member$ 7 ?ris)) then (assert (oav (object malattie)(attribute infettive)(value quarta malattia)(cf 1.0)))
                else (assert (oav (object malattie)(attribute infettive)(value quarta malattia)(cf -0.1))))
            (if (numberp (member$ 8 ?ris)) then (assert (oav (object malattie)(attribute infettive)(value orecchioni)(cf 1.0)))
                else (assert (oav (object malattie)(attribute infettive)(value orecchioni)(cf -0.1))))
            (if (numberp (member$ 9 ?ris)) then (assert (oav (object malattie)(attribute infettive)(value pertosse)(cf 1.0)))
                else (assert (oav (object malattie)(attribute infettive)(value pertosse)(cf -0.1))))))

(defrule altre-malattie
    (not (oav (object malattie)(attribute altre)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino soffre o ha sofferto di alcuna delle seguenti malattie?" crlf
        "1) Gastroenteriti frequenti" crlf "2) Diabete" crlf "3) Cardiopatie" crlf
        "4) Asma o malattie broncopolmonari" crlf "5) Cerebropatie" crlf
        "6) Meningite" crlf "7) Encefalite" crlf "8) Paralisi cerebrale infantile" crlf
        "9) Epilessia" crlf "10) Convulsioni" crlf)
    (printout t "(Indicare i numeri corrispondenti separandoli con uno spazio o digitare NO)" crlf)
    (bind ?ris (ask-question "" 1 2 3 4 5 6 7 8 9 10 no))
    (if (numberp (member$ ns ?ris)) then
            (assert (oav (object malattie)(attribute altre)(value incerto)(cf 0.0)))
        else
            (if (numberp (member$ 1 ?ris)) then (assert (oav (object malattie)(attribute altre)(value gastroenteriti frequenti)(cf 1.0)))
                else (assert (oav (object malattie)(attribute altre)(value gastroenteriti frequenti)(cf -0.2))))
            (if (numberp (member$ 2 ?ris)) then (assert (oav (object malattie)(attribute altre)(value diabete)(cf 1.0)))
                else (assert (oav (object malattie)(attribute altre)(value diabete)(cf -0.2))))
            (if (numberp (member$ 3 ?ris)) then (assert (oav (object malattie)(attribute altre)(value cardiopatie)(cf 1.0)))
                else (assert (oav (object malattie)(attribute altre)(value cardiopatie)(cf -0.2))))
            (if (numberp (member$ 4 ?ris)) then (assert (oav (object malattie)(attribute altre)(value asma malattie broncopolmonari)(cf 1.0)))
                else (assert (oav (object malattie)(attribute altre)(value asma malattie broncopolmonari)(cf -0.2))))
            (if (numberp (member$ 5 ?ris)) then (assert (oav (object malattie)(attribute altre)(value cerebropatie)(cf 1.0)))
                else (assert (oav (object malattie)(attribute altre)(value cerebropatie)(cf -0.2))))
            (if (numberp (member$ 6 ?ris)) then (assert (oav (object malattie)(attribute altre)(value meningite)(cf 1.0)))
                else (assert (oav (object malattie)(attribute altre)(value meningite)(cf -0.2))))
            (if (numberp (member$ 7 ?ris)) then (assert (oav (object malattie)(attribute altre)(value encefalite)(cf 1.0)))
                else (assert (oav (object malattie)(attribute altre)(value encefalite)(cf -0.2))))
            (if (numberp (member$ 8 ?ris)) then (assert (oav (object malattie)(attribute altre)(value paralisi cerebrale infantile)(cf 1.0)))
                else (assert (oav (object malattie)(attribute altre)(value paralisi cerebrale infantile)(cf -0.2))))
            (if (numberp (member$ 9 ?ris)) then (assert (oav (object malattie)(attribute altre)(value epilessia)(cf 1.0)))
                else (assert (oav (object malattie)(attribute altre)(value epilessia)(cf -0.2))))
            (if (numberp (member$ 10 ?ris)) then (assert (oav (object malattie)(attribute altre)(value convulsioni)(cf 1.0)))
                else (assert (oav (object malattie)(attribute altre)(value convulsioni)(cf -0.2))))))

; Affezioni otorinolaringoiatriche
(defrule affezioni-otorinolaringoiatriche
    (not (oav (object affezioni)(attribute otorinolaringoiatriche)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino soffre o ha sofferto di:" crlf)
    (printout t "1) Otiti" crlf "2) Otiti secernenti" crlf "3) Tonsilliti" crlf
        "4) Allergie" crlf "5) Ipoacusia" crlf "6) Raffreddore cronico" crlf)
    (printout t "(Indicare i numeri corrispondenti separandoli con uno spazio o digitare NO)" crlf)
    (bind ?ris (ask-question "" 1 2 3 4 5 6 no))
    (if (numberp (member$ ns ?ris))
        then
            (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value incerto)(cf 0.0)))
        else
            (if (numberp (member$ 1 ?ris)) then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value otiti)(cf 1.0)))
                else (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value otiti)(cf -0.2))))
            (if (numberp (member$ 2 ?ris)) then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value otiti secernenti)(cf 1.0)))
                else (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value otiti secernenti)(cf -0.2))))
            (if (numberp (member$ 3 ?ris)) then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value tonsilliti)(cf 1.0)))
                else (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value tonsilliti)(cf -0.2))))
            (if (numberp (member$ 4 ?ris)) then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value allergie)(cf 1.0)))
                else (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value allergie)(cf -0.2))))
            (if (numberp (member$ 5 ?ris)) then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value ipoacusia)(cf 1.0)))
                else (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value ipoacusia)(cf -0.2))))
            (if (numberp (member$ 6 ?ris)) then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value raffreddore cronico)(cf 1.0)))
                else (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value raffreddore cronico)(cf -0.2))))))

(defrule respira-con-la-bocca
    (not (oav (object affezioni)(attribute otorinolaringoiatriche)(value respira $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino respira con la bocca?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value respira incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value respira con la bocca)(cf 1.0)))
            else (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value respira con il naso)(cf -0.1))))))

(defrule operazioni
    (not (oav (object affezioni)(attribute otorinolaringoiatriche)(value operazioni $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino ha subito operazioni?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value operazioni incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value operazioni)(cf 1.0)))
            else (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value operazioni)(cf -0.1))))))

(defrule sondino
    (not (oav (object affezioni)(attribute otorinolaringoiatriche)(value sondino $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino ha avuto il sondino naso-gastrico?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value sondino incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value sondino naso-gastrico)(cf 1.0)))
            else (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value sondino naso-gastrico)(cf -0.1))))))

(defrule intubazioni
    (not (oav (object affezioni)(attribute otorinolaringoiatriche)(value intubazioni $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino ha subito intubazioni?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value intubazioni incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value intubazioni)(cf 1.0)))
            else (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value intubazioni)(cf -0.1))))))

(defrule uso-prolungato-di-farmaci
    (not (oav (object affezioni)(attribute otorinolaringoiatriche)(value $? farmaci)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino ha fatto o fa uso prolungato di farmaci?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value incerto farmaci)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value uso prolungato di farmaci)(cf 1.0)))
            else (assert (oav (object affezioni)(attribute otorinolaringoiatriche)(value uso prolungato di farmaci)(cf -0.1))))))

(defrule porta-gli-occhiali
    (not (oav (object occhiali)(attribute ha bisogno)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino porta gli occhiali?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object occhiali)(attribute ha bisogno)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object occhiali)(attribute ha bisogno)(value si)(cf 1.0)))
            else (assert (oav (object occhiali)(attribute ha bisogno)(value no)(cf -0.1))))))

(defrule porta-protesi-acustiche
    (not (oav (object protesi acustiche)(attribute ha bisogno)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino porta protesi acustiche?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object protesi acustiche)(attribute ha bisogno)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object protesi acustiche)(attribute ha bisogno)(value si)(cf 1.0)))
            else (assert (oav (object protesi acustiche)(attribute ha bisogno)(value no)(cf -0.1))))))

;; Linguaggio

(defrule prima-lallazione
    (not (oav (object linguaggio)(attribute prima lallazione a)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "A quanti mesi il bambino ha iniziato la lallazione?" crlf
        "1) A 6 mesi" crlf "2) Dopo più di 6 mesi" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object linguaggio)(attribute prima lallazione a)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object linguaggio)(attribute prima lallazione a)(value sei mesi)(cf -0.1)))
            else (assert (oav (object linguaggio)(attribute prima lallazione a)(value oltre sei mesi)(cf 1.0))))))

(defrule prime-parole
    (not (oav (object linguaggio)(attribute prime parole a)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "A quanti mesi il bambino ha detto le prime parole?" crlf
        "1) A 12 mesi" crlf "2) Dopo più di 12 mesi" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object linguaggio)(attribute prime parole a)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then
            (assert (oav (object linguaggio)(attribute prime parole a)(value dodici mesi)(cf -0.1)))
            else (assert (oav (object linguaggio)(attribute prime parole a)(value oltre dodici mesi)(cf 1.0))))))

(defrule frasi-di-due-parole
    (not (oav (object linguaggio)(attribute prime frasi due parole)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "A quanti mesi il bambino ha detto frasi di due parole?" crlf
        "1) A 18 mesi" crlf "2) Dopo più di 18 mesi" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object linguaggio)(attribute prime frasi due parole)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object linguaggio)(attribute prime frasi due parole)(value diciotto mesi)(cf -0.1)))
            else (assert (oav (object linguaggio)(attribute prime frasi due parole)(value oltre diciotto mesi)(cf 1.0))))))

(defrule lingue-parlate-in-famiglia
    (not (oav (object linguaggio)(attribute lingue parlate in famiglia)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "In famiglia, quante lingue si parlano?" crlf
        "1) Una (italiano)" crlf "2) Due (italiano e dialetto)" crlf
        "3) Tre o più" crlf)
    (bind ?ris (ask-question "" 1 2 3))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object linguaggio)(attribute lingue parlate in famiglia)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 3 ?ris)) then
            (assert (oav (object linguaggio)(attribute lingue parlate in famiglia)(value tre o piu)(cf 1.0)))
            else (assert (oav (object linguaggio)(attribute lingue parlate in famiglia)(value due o meno)(cf -0.1))))))

(defrule evoluzione-del-linguaggio
    (not (oav (object linguaggio)(attribute evoluzione)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (bind ?ris (ask-question "L'evoluzione del linguaggio è stata lineare?" "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object linguaggio)(attribute evoluzione)(value incerto)(cf 0.0)))
        else (if (numberp (member$ no ?ris)) then (assert (oav (object linguaggio)(attribute evoluzione)(value non lineare)(cf 1.0)))
            else (assert (oav (object linguaggio)(attribute evoluzione)(value lineare)(cf -0.1))))))

(defrule regressione-pausa-linguaggio
    (oav (object linguaggio)(attribute evoluzione)(value non lineare)(cf ?c1))
    (test (< ?c1 0.0))
    (not (oav (object linguaggio)(attribute evoluzione)(value ~lineare)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il linguaggio è:" crlf "1) Regredito" crlf "2) Non avanzato" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object linguaggio)(attribute evoluzione)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object linguaggio)(attribute evoluzione)(value regredito)(cf 1.0)))
                (assert (oav (object linguaggio)(attribute evoluzione)(value non avanzato)(cf -0.1))))
            (if (numberp (member$ 2 ?ris)) then (assert (oav (object linguaggio)(attribute evoluzione)(value regredito)(cf -0.1)))
                (assert (oav (object linguaggio)(attribute evoluzione)(value non avanzato)(cf 1.0))))))

;; Socialità

(defrule nido-frequenza
    (not (oav (object nido)(attribute frequentato)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (bind ?ris (ask-question "Frequenta o ha frequentato il nido?" "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object nido)(attribute frequentato)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object nido)(attribute frequentato)(value si)(cf 0.1)))
            else (assert (oav (object nido)(attribute frequentato)(value no)(cf -0.1))))))

(defrule nido-ambientarsi
    (oav (object nido)(attribute frequentato)(value si)(cf ?c1))
    (not (oav (object socialita)(attribute nido fatica ad ambientarsi)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Fatica o ha faticato ad ambientarsi al nido?" crlf
        "1) Solo all'inizio" crlf "2) Tutto il tempo" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object socialita)(attribute nido fatica ad ambientarsi)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object socialita)(attribute nido fatica ad ambientarsi)(value solo inizialmente)(cf -0.1)))
            else (assert (oav (object socialita)(attribute nido fatica ad ambientarsi)(value tutto il tempo)(cf 1.0))))))

(defrule scuola-materna-frequenza
    (not (oav (object scuola materna)(attribute frequentato)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (bind ?ris (ask-question "Frequenta o ha frequentato la scuola materna?" "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object scuola materna)(attribute frequentato)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object scuola materna)(attribute frequentato)(value si)(cf 0.1)))
            else (assert (oav (object scuola materna)(attribute frequentato)(value no)(cf -0.1))))))

(defrule scuola-materna-ambientarsi
    (oav (object scuola materna)(attribute frequentato)(value si)(cf ?c1))
    (not (oav (object socialita)(attribute scuola materna fatica ad ambientarsi)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Fatica o ha faticato ad ambientarsi alla scuola materna?" crlf
        "1) Solo all'inizio" crlf "2) Tutto il tempo" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object socialita)(attribute scuola materna fatica ad ambientarsi)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object socialita)(attribute scuola materna fatica ad ambientarsi)(value solo inizialmente)(cf -0.1)))
            else (assert (oav (object socialita)(attribute scuola materna fatica ad ambientarsi)(value tutto il tempo)(cf 1.0))))))

(defrule personalita
    (not (oav (object socialita)(attribute ha personalita)(value $?)(cf ?c1)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino è:" crlf "1) Molto vivace" crlf "2) Vivace" crlf
        "3) Tranquillo" crlf "4) Indifferente" crlf "5) Variabile" crlf)
    (bind ?ris (ask-question "" 1 2 3 4 5))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object socialita)(attribute ha personalita)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 4 ?ris)) then (assert (oav (object socialita)(attribute ha personalita)(value indifferente)(cf 1.0)))
                else (assert (oav (object socialita)(attribute ha personalita)(value indifferente)(cf -0.1))))
            (if (numberp (member$ 5 ?ris)) then (assert (oav (object socialita)(attribute ha personalita)(value variabile)(cf 1.0)))
                else (assert (oav (object socialita)(attribute ha personalita)(value variabile)(cf -0.1))))))

(defrule gioco-preferenze
    (not (oav (object socialita)(attribute gioco con chi)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino preferisce giocare:" crlf "1) Da solo" crlf "2) Con altri bambini" crlf
        "3) Con fratelli" crlf "4) Con adulti" crlf "5) Con tutti" crlf "6) Non gioca" crlf)
    (bind ?ris (ask-question "" 1 2 3 4 5 6))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object socialita)(attribute gioco con chi)(value incerto)(cf 0.0)))
        else (if (or (numberp (member$ 1 ?ris))(numberp (member$ 6 ?ris))) then
            (assert (oav (object socialita)(attribute gioco con chi)(value problematico)(cf 1.0)))
                else (assert (oav (object socialita)(attribute gioco con chi)(value problematico)(cf -0.1))))))

(defrule gioca-come
    (not (oav (object socialita)(attribute gioco come)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino, quando gioca:" crlf "1) È tranquillo" crlf "2) Picchia gli altri" crlf
        "3) Viene picchiato" crlf "4) Fa dispetti" crlf "5) Si isola" crlf "6) Vuole sempre comandare" crlf
        "7) Si sottomette" crlf "8) Gioca insieme agli altri" crlf )
    (bind ?ris (ask-question "" 1 2 3 4 5 6 7 8))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object socialita)(attribute gioco come)(value incerto)(cf 0.0)))
        else (if (or (numberp (member$ 2 ?ris))(numberp (member$ 3 ?ris))(numberp (member$ 5 ?ris))) then
            (assert (oav (object socialita)(attribute gioco come)(value problematico)(cf 1.0)))
                else (assert (oav (object socialita)(attribute gioco come)(value problematico)(cf -0.1))))))

(defrule insegnanti-rapporti
    (not (oav (object socialita)(attribute insegnanti rapporto)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Che rapporti ha con gli insegnanti?" crlf "1) Positivi" crlf
        "2) Negativi" crlf "3) Altalenanti" crlf)
    (bind ?ris (ask-question "" 1 2 3))
    (if (numberp (member$ ns ?ris)) then
        (assert (oav (object socialita)(attribute insegnanti rapporto)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object socialita)(attribute insegnanti rapporto)(value positivo)(cf -0.1)))
            else (if (numberp (member$ 2 ?ris)) then (assert (oav (object socialita)(attribute insegnanti rapporto)(value negativo)(cf 1.0)))
                else (assert (oav (object socialita)(attribute insegnanti rapporto)(value negativo)(cf 0.5)))))))

(defrule si-stanca-a-studiare
    (not (oav (object studio a scuola)(attribute si stanca facilmente)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "A scuola si stanca facilmente a studiare?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object studio a scuola)(attribute si stanca facilmente)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object studio a scuola)(attribute si stanca facilmente)(value si)(cf 1.0)))
            else (assert (oav (object studio a scuola)(attribute si stanca facilmente)(value no)(cf -0.1))))))

(defrule difficolta-studio
    (oav (object studio a scuola)(attribute si stanca facilmente)(value si)(cf ?))
    (not (oav (object studio a scuola)(attribute difficolta in)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Ha difficoltà in:" crlf "1) Lettura" crlf
        "2) Scrittura" crlf "3) Calcolo" crlf)
    (bind ?ris (ask-question "(Indicare i numeri corrispondenti separandoli con uno spazio o digitare NO)" "" 1 2 3 no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object studio a scuola)(attribute difficolta in)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object studio a scuola)(attribute difficolta in)(value lettura)(cf 1.0)))
                else (assert (oav (object studio a scuola)(attribute difficolta in)(value lettura)(cf -0.1))))
            (if (numberp (member$ 2 ?ris)) then (assert (oav (object studio a scuola)(attribute difficolta in)(value scrittura)(cf 1.0)))
                else (assert (oav (object studio a scuola)(attribute difficolta in)(value scrittura)(cf -0.1))))
            (if (numberp (member$ 3 ?ris)) then (assert (oav (object studio a scuola)(attribute difficolta in)(value calcolo)(cf 1.0)))
                else (assert (oav (object studio a scuola)(attribute difficolta in)(value calcolo)(cf -0.1))))))

(defrule viene-seguito-a-casa
    (not (oav (object studio a casa)(attribute viene seguito)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Viene seguito nello svolgimento dei compiti a casa?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object studio a casa)(attribute viene seguito)(value incerto)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object studio a casa)(attribute viene seguito)(value si)(cf 1.0)))
            else (assert (oav (object studio a casa)(attribute viene seguito)(value si)(cf -0.1))))))

(defrule difficolta-varie
    (not (oav (object difficolta)(attribute di)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Avete notato difficoltà di:" crlf "1) Vista" crlf
        "2) Udito" crlf "3) Comportamento" crlf "4) Comprensione verbale" crlf
        "5) Attenzione/Concentrazione" crlf "6) Memoria" crlf "7) Aspetto socio-relazionale" crlf)
    (bind ?ris (ask-question "(Indicare i numeri corrispondenti separandoli con uno spazio o digitare NO)" "" 1 2 3 4 5 6 7 no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object difficolta)(attribute di)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object difficolta)(attribute di)(value vista)(cf 1.0)))
            else (assert (oav (object difficolta)(attribute di)(value vista)(cf -0.1))))
        (if (numberp (member$ 2 ?ris)) then (assert (oav (object difficolta)(attribute di)(value udito)(cf 1.0)))
            else (assert (oav (object difficolta)(attribute di)(value udito)(cf -0.1))))
        (if (numberp (member$ 3 ?ris)) then (assert (oav (object difficolta)(attribute di)(value comportamento)(cf 1.0)))
            else (assert (oav (object difficolta)(attribute di)(value comportamento)(cf -0.1))))
        (if (numberp (member$ 4 ?ris)) then (assert (oav (object difficolta)(attribute di)(value comprensione verbale)(cf 1.0)))
            else (assert (oav (object difficolta)(attribute di)(value comprensione verbale)(cf -0.1))))
        (if (numberp (member$ 5 ?ris)) then (assert (oav (object difficolta)(attribute di)(value attenzione concentrazione)(cf 1.0)))
            else (assert (oav (object difficolta)(attribute di)(value attenzione concentrazione)(cf -0.1))))
        (if (numberp (member$ 6 ?ris)) then (assert (oav (object difficolta)(attribute di)(value memoria)(cf 1.0)))
            else (assert (oav (object difficolta)(attribute di)(value memoria)(cf -0.1))))
        (if (numberp (member$ 7 ?ris)) then (assert (oav (object difficolta)(attribute di)(value aspetto socio-relazionale)(cf 1.0)))
            else (assert (oav (object difficolta)(attribute di)(value aspetto socio-relazionale)(cf -0.1))))))

;; Disfonia

(defrule patologie-vocali
    (not (oav (object familiarita)(attribute comprende)(value $? patologie vocali)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "In famiglia sono o sono stati presenti casi di patologie vocali?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object familiarita)(attribute comprende)(value incerto patologie vocali)(cf 0.0)))
        else (if (numberp (member$ si ?ris)) then (assert (oav (object familiarita)(attribute comprende)(value patologie vocali)(cf 1.0)))
            else (assert (oav (object familiarita)(attribute comprende)(value patologie vocali)(cf -0.1))))))

(defrule patologie-vocali-quali
    (not (oav (object familiarita)(attribute patologie vocali)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Il bambino ha o ha avuto:" crlf "1) Anomalie congenite laringee" crlf
        "2) Disturbo dello sviluppo puberale" crlf "3) Flogosi recidivante delle vie aeree" crlf
        "4) Patologie metaboliche endocrine" crlf "5) Ipoacusie" crlf)
    (bind ?ris (ask-question "(Indicare i numeri corrispondenti separandoli con uno spazio o digitare NO)" "" 1 2 3 4 5 no))
    (if (numberp (member$ ns ?ris))
        then (assert (oav (object familiarita)(attribute patologie vocali)(value incerto)(cf 0.0)))
        else (if (numberp (member$ 1 ?ris)) then (assert (oav (object familiarita)(attribute patologie vocali)(value anomalie congenite laringee)(cf 1.0)))
                else (assert (oav (object familiarita)(attribute patologie vocali)(value anomalie congenite laringee)(cf -0.2))))
            (if (numberp (member$ 1 ?ris)) then (assert (oav (object familiarita)(attribute patologie vocali)(value disturbo dello sviluppo puberale)(cf 1.0)))
                else (assert (oav (object familiarita)(attribute patologie vocali)(value disturbo dello sviluppo puberale)(cf -0.2))))
            (if (numberp (member$ 1 ?ris)) then (assert (oav (object familiarita)(attribute patologie vocali)(value flogosi recidivante delle vie aeree)(cf 1.0)))
                else (assert (oav (object familiarita)(attribute patologie vocali)(value flogosi recidivante delle vie aeree)(cf -0.2))))
            (if (numberp (member$ 1 ?ris)) then (assert (oav (object familiarita)(attribute patologie vocali)(value patologie metaboliche endocrine)(cf 1.0)))
                else (assert (oav (object familiarita)(attribute patologie vocali)(value patologie metaboliche endocrine)(cf -0.2))))
            (if (numberp (member$ 1 ?ris)) then (assert (oav (object familiarita)(attribute patologie vocali)(value ipoacusie)(cf 1.0)))
                else (assert (oav (object familiarita)(attribute patologie vocali)(value ipoacusie)(cf -0.2))))))

(defrule sforzi-vocali
    (not (oav (object disfonia)(attribute fa sforzi vocali)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Fa sforzi vocali?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object disfonia)(attribute fa sforzi vocali)(value incerto)(cf 0.0)))
    else (if (numberp (member$ si ?ris)) then (assert (oav (object disfonia)(attribute fa sforzi vocali)(value si)(cf 1.0)))
            else (assert (oav (object disfonia)(attribute fa sforzi vocali)(value no)(cf -0.1))))))

(defrule atteggiamenti
    (oav (object disfonia)(attribute fa sforzi vocali)(value si)(cf ?c1))
    (not (oav (object disfonia)(attribute ha atteggiamenti)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Ha atteggiamenti:" crlf
        "1) Di tensione" crlf "2) Di aggressività" crlf
        "3) Di remissività" crlf "4) Eccessivamente detesi" crlf)
    (bind ?ris (ask-question "(Indicare i numeri corrispondenti separandoli con uno spazio o digitare NO)" "" 1 2 3 4 no))
    (if (numberp (member$ ns ?ris)) then
        (assert (oav (object disfonia)(attribute ha atteggiamenti)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then (assert (oav (object disfonia)(attribute ha atteggiamenti)(value tensione)(cf 1.0)))
            else (assert (oav (object disfonia)(attribute ha atteggiamenti)(value tensione)(cf -0.1))))
        (if (numberp (member$ 1 ?ris)) then (assert (oav (object disfonia)(attribute ha atteggiamenti)(value aggressivi)(cf 1.0)))
            else (assert (oav (object disfonia)(attribute ha atteggiamenti)(value aggressivi)(cf -0.1))))
        (if (numberp (member$ 1 ?ris)) then (assert (oav (object disfonia)(attribute ha atteggiamenti)(value remissivi)(cf 1.0)))
            else (assert (oav (object disfonia)(attribute ha atteggiamenti)(value remissivi)(cf -0.1))))
        (if (numberp (member$ 1 ?ris)) then (assert (oav (object disfonia)(attribute ha atteggiamenti)(value eccessivamente detesi)(cf 1.0)))
            else (assert (oav (object disfonia)(attribute ha atteggiamenti)(value eccessivamente detesi)(cf -0.1))))))

(defrule canta
    (oav (object disfonia)(attribute fa sforzi vocali)(value si)(cf ?c1))
    (not (oav (object disfonia)(attribute sforzi vocali canta)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Canta?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object disfonia)(attribute sforzi vocali canta)(value incerto)(cf 0.0)))
    else (if (numberp (member$ si ?ris)) then (assert (oav (object disfonia)(attribute sforzi vocali canta)(value si)(cf 1.0)))
            else (assert (oav (object disfonia)(attribute fa sforzi vocali)(value canta)(cf -0.1))))))

(defrule canta-quanto
    (oav (object disfonia)(attribute sforzi vocali canta)(value si)(cf ?c1))
    (test (> ?c1 0.0))
    (not (oav (object disfonia)(attribute quanto canta)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Canta:" crlf "1) Spesso" crlf "2) In coro" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object disfonia)(attribute quanto canta)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then (assert (oav (object disfonia)(attribute quanto canta)(value spesso)(cf 1.0)))
            else (assert (oav (object disfonia)(attribute quanto canta)(value spesso)(cf -0.1))))
        (if (numberp (member$ 2 ?ris)) then (assert (oav (object disfonia)(attribute quanto canta)(value in coro)(cf 1.0)))
            else (assert (oav (object disfonia)(attribute quanto canta)(value in coro)(cf -0.1))))))

(defrule muta-vocale
    (not (oav (object disfonia)(attribute muta vocale)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Muta vocale?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object disfonia)(attribute muta vocale)(value incerto)(cf 0.0)))
    else (if (numberp (member$ si ?ris)) then (assert (oav (object disfonia)(attribute muta vocale)(value si)(cf 1.0)))
        else (assert (oav (object disfonia)(attribute muta vocale)(value si)(cf -0.1))))))

(defrule respiratore-orale
    (not (oav (object disfonia)(attribute respiratore orale)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Fa o ha fatto uso di respiratore orale?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object disfonia)(attribute respiratore orale)(value incerto)(cf 0.0)))
    else (if (numberp (member$ si ?ris)) then (assert (oav (object disfonia)(attribute respiratore orale)(value si)(cf 1.0)))
        else (assert (oav (object disfonia)(attribute respiratore orale)(value si)(cf -0.1))))))

(defrule tosse-sovente
    (not (oav (object disfonia)(attribute tosse sovente)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Ha tosse sovente?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object disfonia)(attribute tosse sovente)(value incerto)(cf 0.0)))
    else (if (numberp (member$ si ?ris)) then (assert (oav (object disfonia)(attribute tosse sovente)(value si)(cf 1.0)))
        else (assert (oav (object disfonia)(attribute tosse sovente)(value si)(cf -0.1))))))

(defrule raschiarsi-la-gola
    (not (oav (object disfonia)(attribute gola raschiarsi)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Necessita di raschiarsi la gola?" crlf
        "1) Si spesso" crlf "2) No mai" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object disfonia)(attribute gola raschiarsi)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then (assert (oav (object disfonia)(attribute gola raschiarsi)(value si)(cf 1.0)))
        else (assert (oav (object disfonia)(attribute gola raschiarsi)(value no)(cf -0.1))))))

(defrule gola-bruciore
    (not (oav (object disfonia)(attribute gola bruciore)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Ha sensazione di bruciare in gola?" crlf
        "1) Si spesso" crlf "2) No mai" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object disfonia)(attribute gola bruciore)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then (assert (oav (object disfonia)(attribute gola bruciore)(value si)(cf 1.0)))
        else (assert (oav (object disfonia)(attribute gola bruciore)(value si)(cf -0.1))))))

(defrule gola-costrizione
    (not (oav (object disfonia)(attribute gola bruciore)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Ha sensazione di costrizione in gola?" crlf
        "1) Si spesso" crlf "2) No mai" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object disfonia)(attribute gola costrizione)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then (assert (oav (object disfonia)(attribute gola costrizione)(value si)(cf 1.0)))
        else (assert (oav (object disfonia)(attribute gola costrizione)(value si)(cf -0.1))))))

(defrule gola-corpo-estraneo
    (not (oav (object disfonia)(attribute gola corpo estraneo)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Ha sensazione di avere un corpo estraneo in gola?" crlf
        "1) Si spesso" crlf "2) No mai" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object disfonia)(attribute gola corpo estraneo)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then (assert (oav (object disfonia)(attribute gola corpo estraneo)(value si)(cf 1.0)))
        else (assert (oav (object disfonia)(attribute gola corpo estraneo)(value si)(cf -0.1))))))

(defrule crampi-al-collo
    (not (oav (object disfonia)(attribute crampi a collo muscoli)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Ha crampi al collo o muscolari?" crlf
        "1) Si spesso" crlf "2) No mai" crlf)
    (bind ?ris (ask-question "" 1 2))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object disfonia)(attribute crampi a collo muscoli)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then (assert (oav (object disfonia)(attribute crampi a collo muscoli)(value si)(cf 1.0)))
        else (assert (oav (object disfonia)(attribute crampi a collo muscoli)(value si)(cf -0.1))))))

(defrule traumi
    (not (oav (object disfonia)(attribute traumi collo torace addome)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Ha avuto traumi o operazioni a collo, torace o addome?" crlf)
    (bind ?ris (ask-question "" si no))
    (if (numberp (member$ ns ?ris)) then (assert (oav (object disfonia)(attribute traumi collo torace addome)(value incerto)(cf 0.0)))
    else (if (numberp (member$ si ?ris)) then (assert (oav (object disfonia)(attribute traumi collo torace addome)(value si)(cf 1.0)))
        else (assert (oav (object disfonia)(attribute traumi collo torace addome)(value si)(cf -0.1))))))

(defrule parla-con-voce
    (not (oav (object disfonia)(attribute parla con voce)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "Parla con voce:" crlf "1) Rauca" crlf
        "2) Afona" crlf "3) Molto alta" crlf)
    (bind ?ris (ask-question "(Indicare i numeri corrispondenti separandoli con uno spazio o digitare NO)" "" 1 2 3 no))
    (if (numberp (member$ ns ?ris)) then
        (assert (oav (object disfonia)(attribute parla con voce)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then (assert (oav (object disfonia)(attribute parla con voce)(value rauca)(cf 1.0)))
        else (assert (oav (object disfonia)(attribute parla con voce)(value rauca)(cf -0.1))))
        (if (numberp (member$ 2 ?ris)) then (assert (oav (object disfonia)(attribute parla con voce)(value afona)(cf 1.0)))
            else (assert (oav (object disfonia)(attribute parla con voce)(value afona)(cf -0.1))))
        (if (numberp (member$ 3 ?ris)) then (assert (oav (object disfonia)(attribute parla con voce)(value molto alta)(cf 1.0)))
            else (assert (oav (object disfonia)(attribute parla con voce)(value molto alta)(cf -0.1))))))

(defrule soggetto-a
    (not (oav (object disfonia)(attribute soggetto a)(value $?)(cf ?)))
    (oav (object diagnosi)(attribute esito)(value $?)(cf ?cf1&:(< ?cf1 0.5)))
    (anamnesi (stato start))
    =>
    (printout t "È soggetto a:" crlf
        "1) Brusche variazioni di temperatura" crlf
        "2) Stimoli sonori intensi o prolungati" crlf)
    (bind ?ris (ask-question "(Indicare i numeri corrispondenti separandoli con uno spazio o digitare NO)" "" 1 2 no))
    (if (numberp (member$ ns ?ris)) then
        (assert (oav (object disfonia)(attribute soggetto a)(value incerto)(cf 0.0)))
    else (if (numberp (member$ 1 ?ris)) then (assert (oav (object disfonia)(attribute soggetto a)(value brusche variazioni di temperatura)(cf 1.0)))
        else (assert (oav (object disfonia)(attribute soggetto a)(value brusche variazioni di temperatura)(cf -0.1))))
        (if (numberp (member$ 2 ?ris)) then (assert (oav (object disfonia)(attribute soggetto a)(value stimoli sonori intensi prolungati)(cf 1.0)))
            else (assert (oav (object disfonia)(attribute soggetto a)(value stimoli sonori intensi prolungati)(cf -0.1))))))


