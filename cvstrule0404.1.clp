;;define symptom template to express the symptom information

(deftemplate MAIN::symptom
   (multislot symname (type SYMBOL))
   (slot value)
   (slot CE (type FLOAT) (range -1.0 1.0) (default 0.0)))

;;define patient template to express the patient information

(deftemplate MAIN::patient
   (multislot pname (type SYMBOL))
   (slot age (type NUMBER))
   (slot sex (allowed-values male female))
   (slot CVSTCE (type FLOAT) (range 0.0 1.0) (default 0.0)))

(defrule MAIN::initial-ruleselect
   (declare (salience 10))
=>
   (assert (step 1))
)

;;=====rule1: neurologic defect(0.35) and hight-voltage cranial(0.35)  

(defrule MAIN::is-neurologic-defect
   (declare (salience 20))
   (or (symptom (symname dyskinesia) (value exist))
       (symptom (symname anaesthesia) (value exist))
       (symptom (symname aphasia) (value exist))
       (symptom (symname hemianopsia) (value exist))
   )
=>
   (assert (symptom (symname neurologic) (value defect) (CE 0.35)))
)

(defrule MAIN::is-cranial-hight-voltage
   (declare (salience 20))
   (and (symptom (symname optic nerve head edema) (value exist))
        (or (symptom (symname headache) (value exist))
            (symptom (symname emesis) (value exist))
        )
   )
=>
   (assert (symptom (symname cranial) (value hight-voltage) (CE 0.35)))
)

(defrule MAIN::neurologic-and-cranial
   ?s <- (step 1)
   (symptom (symname neurologic) (value defect) (CE ?ce1))
   (symptom (symname cranial) (value hight-voltage) (CE ?ce2))
   ?p <- (patient (pname ?name) (CVSTCE ?ce))
=>
   (retract ?s)
   (assert (step 2))
   (if (> (+ ?ce1 ?ce2) ?ce)
    then 
      (modify ?p (CVSTCE (+ ?ce ?ce1 ?ce2)))
   )
)

(defrule MAIN::no-neurologic-and-cranial
   ?s <- (step 1)
   (or (not (symptom (symname neurologic)))
       (not (symptom (symname cranial)))
   )
=>
   (retract ?s)
   (assert (step 2))
)

;;=====rule2: epileptic seizure

(defrule MAIN::is-epileptic-seizure
   (declare (salience 20))
   (and (symptom (symname epilepsy) (value exist))
        (or (symptom (symname dyskinesia) (value exist))
            (symptom (symname anaesthesia) (value exist))
        )
   )
=>
   (assert (symptom (symname epileptic seizure) (value exist) (CE 0.4)))
)

(defrule MAIN::only-epileptic
   ?s <- (step 2)
   (and (not (symptom (symname perinatal stage) (value exist)))
        (symptom (symname epileptic seizure) (value exist) (CE ?ce2))
        ?p <- (patient (pname ?name) (CVSTCE ?ce1))
   )
=>
   (retract ?s)
   (assert (step 3))
   (modify ?p (CVSTCE (- (+ ?ce1 ?ce2) (* ?ce1 ?ce2))))
)

(defrule MAIN::is-perinatal-stage-and-epileptic
   ?s <- (step 2)
   (symptom (symname perinatal stage) (value exist))
   (symptom (symname epileptic seizure) (value exist) (CE ?ce2))
   ?p <- (patient (pname ?name) (CVSTCE ?ce1))
=>
   (retract ?s)
   (assert (step 3))
   (modify ?p (CVSTCE (- (+ ?ce1 ?ce2 0.08) (* ?ce1 ?ce2)))) 
)

(defrule MAIN::no-epileptic
   ?s <- (step 2)
   (not (symptom (symname epileptic seizure)))
=>
   (retract ?s)
   (assert (step 3))
)

;;=====rule3:cranial hight voltage and epileptic seizure and conscious 
;;           diaturbance and dysphrenia

(defrule MAIN::is-dysphrenia
   (declare (salience 20))
   (or (symptom (symname delusion) (value exist))
       (symptom (symname acousma) (value exist))
       (symptom (symname will-lysis) (value exist))
       (symptom (symname conduct disorders) (value exist))
   )
=>
   (assert (symptom (symname dysphrenia) (value exist) (CE 0.15)))
)

(defrule MAIN::is-consciousness-disturbance
   (declare (salience 20))
   (or (symptom (symname aphasia) (value exist))
       (symptom (symname anaesthesia) (value exist))
       (symptom (symname dysarthria) (value exist))
       (symptom (symname hallucination) (value exist))
   )
=>
   (assert (symptom (symname consciousness disturbance) (value exist) (CE 0.15)))
)

(defrule MAIN::cranial-syndrome-epileptic
   ?s <- (step 3)
   (and (symptom (symname cranial) (value hight-voltage))
        (symptom (symname epileptic seizure) (value exist))
        (or (symptom (symname consciousness disturbance) (value exist) (CE ?ce2))
            (symptom (symname dysphrenia) (value exist) (CE ?ce2))
        )
   )
   ?p <- (patient (pname ?name) (CVSTCE ?ce1))
=>
   (retract ?s)
   (assert (step 4) (judge children) (judge women))
   (modify ?p (CVSTCE (+ ?ce1 0.08))) 
)

(defrule MAIN::no-cranial-syndrome-epileptic
   ?s <- (step 3)
   (or (not (symptom (symname cranial) (value hight-voltage)))
       (not (symptom (symname epileptic seizure) (value exist)))
       (not (or (symptom (symname consciousness disturbance) (value exist))
                (symptom (symname dysphrenia) (value exist)))
       )
   )
=>
   (retract ?s)
   (assert (step 4) (judge children) (judge women))
)

;;=====rule4: is children and infection or women use contraceptive 

(defrule MAIN::is-children-and-infection
   (declare (salience 20))
   ?s <- (step 4)
   ?c <- (judge children)
   ?p <- (patient (age ?age) (CVSTCE ?ce))
   (test (< ?age 18))
   (symptom (symname face infection) (value exist))
=>
   (if (> ?ce 0.5)
   then
      (if (< ?ce 0.9) 
      then
         (modify ?p (CVSTCE (+ ?ce 0.1)))
      else
         (modify ?p (CVSTCE (+ ?ce 0.05)))
      ) 
   )
   (retract ?c)
)

(defrule MAIN::is-women-and-contraceptive
   (declare (salience 20))   
   ?s <- (step 4)
   ?w <- (judge women)
   ?p <- (patient (age ?age) (sex female) (CVSTCE ?ce))
   (test (> ?age 18))
   (symptom (symname using contraceptive) (value exist))
=>
   (if (> ?ce 0.3)
   then
      (if (< ?ce 0.9) 
      then
         (modify ?p (CVSTCE (+ ?ce 0.2)))
      else
         (modify ?p (CVSTCE (+ ?ce 0.06)))
      )
   )
   (retract ?w)
)

(defrule MAIN::next-step
   ?s <- (step 4)
=>
   (retract ?s)
   (assert (step 5))
)

;;=====rule5: eyes examination  

(defrule MAIN::handle-middle-fact1
   (step 5)
   ?c <- (judge children)
=>
   (retract ?c)
)

(defrule MAIN::handle-middle-fact2
   (step 5)
   ?w <- (judge women)
=>
   (retract ?w)
)

(defrule MAIN::is-infection
   (declare (salience 20)) 
   (or (symptom (symname face infection) (value exist))
       (symptom (symname otitis media) (value exist))
       (symptom (symname mastoiditis) (value exist))
       (symptom (symname meningitis) (value exist))
       (symptom (symname nasosinusitis) (value exist)) 
   )
=>
   (assert (symptom (symname infection) (value exist) (CE 0.1)))
)

(defrule MAIN::is-eye-anomaly
   (declare (salience 20))
   (or (symptom (symname blepharoptosis) (value exist))
       (symptom (symname eye movement limitation) (value exist))
       (symptom (symname mydriasis) (value exist))
       (symptom (symname corneal reflection disappear) (value exist))
       (symptom (symname light reflex disappear) (value exist)) 
   )
=>
   (assert (symptom (symname eye anomaly) (value exist) (CE 0.1)))
)

(defrule MAIN::infection-and-eye-anomaly
   ?s <- (step 5)
   (symptom (symname cranial) (value hight-voltage) (CE 0.35))
   (symptom (symname consciousness disturbance) (value exist) (CE 0.15))
   (symptom (symname eye anomaly) (value exist) (CE 0.1))
   (symptom (symname infection) (value exist) (CE 0.1))
   ?p <- (patient (CVSTCE ?ce))
=>
   (retract ?s)
   (assert (step 6))
   (if (< ?ce 0.9)
   then
      (modify ?p (CVSTCE 0.9))
   )
)

(defrule MAIN::no-infection-or-eye-anomaly
   ?s <- (step 5)
   (or (not (symptom (symname cranial) (value hight-voltage)))
       (not (symptom (symname consciousness disturbance) (value exist)))
       (not (symptom (symname eye anomaly) (value exist)))
       (not (symptom (symname infection) (value exist)))
   )
=> 
   (retract ?s)
   (assert (step 6))
)

;;=====rule6: hypertension or hyperlipidemia or hyperglycemia

(defrule MAIN::three-hight
   ?s <- (step 6)
   (or (symptom (symname hypertension) (value exist))
       (symptom (symname hyperlipidemia) (value exist))
       (symptom (symname hyperglycemia) (value exist))
   )
   ?p <- (patient (CVSTCE ?ce))
=> 
   (retract ?s)
   (assert (step 7))
   (modify ?p (CVSTCE (/ ?ce 2)))
)

(defrule MAIN::no-three-hight
   ?s <- (step 6)
   (and (not (symptom (symname hypertension) (value exist)))
        (not (symptom (symname hyperlipidemia) (value exist)))
        (not (symptom (symname hyperglycemia) (value exist)))
   )
=>
   (retract ?s)
   (assert (step 7))
)

;;=====rule7:D-dimer content

(defrule MAIN::d-dimer-increase
   ?s <- (step 7)
   (symptom (symname d-dimer increase) (value exist))
   ?p <- (patient (CVSTCE ?ce))
=>
   (retract ?s)
   (assert (step 8))
   (if (< ?ce 0.5)
   then 
      (modify ?p (CVSTCE (+ ?ce 0.5)))
   else 
      (if (< ?ce 0.9)
      then
         (modify ?p (CVSTCE (+ ?ce 0.1)))
      else
         (modify ?p (CVSTCE (+ ?ce 0.02)))
      )
   )
)

(defrule MAIN::no-d-dimer-increase
   ?s <- (step 7)
   (not (symptom (symname d-dimer increase) (value exist)))
=>
   (retract ?s)
   (assert (step 8))
)

;;=====rule8: CT and CTV
















