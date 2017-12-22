(define (domain western-duel-domain)

    (:types   s-elmnt plan-elmnt intrvl cam-param integer - object
		step literal - plan-elmnt
		step-s step-d - step
		step-c - step-d
		operator-type - plan-elmnt
		literal-s literal-d - literal
		movable-thing - s-elmnt
		person thing - movable-thing
		place - s-elmnt
		gun - thing
		distance - integer
		virtual-shot-type - object
		segment - object
		scale fov angle orient - cam-param
		)
		
	(:constants
		start mid end - segment
		low eye high - angle
		ecu cu med full wide ewide - scale
		behind front right left front-right front-left behind-right behind-left - orient
		0 1 - integer
		12 25 36 48 60 - fov
	)
		
    (:predicates
		(has ?c - person ?t - thing)
        (at ?thing - movable-thing ?place - place)
        (= ?o1 ?o2 - object)
		(facing ?c1 ?c2 - person)
		(alive ?c - person)
		(is-shot ?c - person)
		(holstered ?g - gun)
		(arg ?i - integer ?s - plan-elmnt ?o - object)
		(fired-at ?t - movable-thing)
		(distance-between ?s1 ?s2 - s-elmnt)
		(less-than ?d - distance ?d2 - distance)
		(can-show ?cam - virtual-shot-cam ?p - place)
		(bel ?p - plan-elmnt)
		(bel-alu ?p - plan-elmnt)
		(obs-alu ?p - plan-elmnt)
		(obs-seg-alu ?s - step ?m - segment)
		(obs-seg ?s - step-s ?m - segment)
		(obs ?p - plan-elmnt)
		(obs-seg-cntg ?s - step-s ?m - segment)
		(cntg ?d1 ?d2 - step-d)
		(play ?s - step-s)
		(play-seg ?s - step-s ?m - segment)
		(effect ?s - step ?l - literal)
		(precond ?s - step ?l - literal)
		(preconds ?s - step)
		(linked-by ?s ?t - step ?l - literal)
		(< ?s1 ?s2 - step)
		(alu ?i - intrvl) (fol ?i - intrvl) (dur ?i - intrvl)
		(has-scale ?s - step-c ?sc - scale)
		(has-angle ?s - step-c ?a - angle)
		(has-fov ?s - step-c ?f - integer)
		(has-orient ?s - step ?ort - orient)
		(type ?s - step ?t - operator-type)
        )
		
                    
    (:action strut
        :parameters (?c - person ?p1 ?p2 - place)
        :precondition (and (at ?c ?p1) (alive ?c) (not (= ?p1 ?p2)) (not (is-shot ?c)))
        :effect(and (not (at ?c ?p1)) (at ?c ?p2))
    )
                    
    (:action run
        :parameters (?c - person ?p1 ?p2 - place)
        :precondition (and (at ?c ?p1) (alive ?c) (not (= ?p1 ?p2)) (not (is-shot ?c)))
        :effect(and (not (at ?c ?p1)) (at ?c ?p2))
    )
		
	(:action call
		:parameters (?c - person)
		:precondition (alive ?c)
		:effect ()
	)
	
	(:action turn-to
		:parameters (?c - person ?c2 - person)
		:precondition (and (alive ?c) (not (= ?c ?c2)))
		:effect (facing ?c ?c2)
	)
	
	(:action draw-gun
		:parameters (?c - person ?g - gun)
		:precondition (and (alive ?c) (has ?c ?g) (holstered ?g))
		:effect(not (holstered ?g))
	)
	
	(:action fire-gun
		:parameters (?c - person ?g - gun ?t - movable-thing)
		:precondition (and (alive ?c) (not (holstered ?g)) (has ?c ?g) (not (is-shot ?c)))
		:effect (fired-at ?t)
	)
	
	(:action get-shot
		:parameters (?c1 ?c2 - person ?dist-between ?dist-criteria - distance)
		:precondition (and  (fired-at ?c2)
							(less-than ?dist-between ?dist-criteria))
		:effect (is-shot ?c2)
	)
	
	(:action fall-and-die
		:parameters (?c - person)
		:precondition (is-shot ?c)
		:effect (not (alive ?c))
	)
	
	(:action cam-start-shot
		:parameters (?s - step-s ?sc - scale ?ort - orient )
		:precondition (bel (preconds ?s))
		:effect (and (obs-seg ?s end) (bel ?s))
		:decomp (:sub-params () :requirements (play-seg ?s end))
	)
	
	(:action cam-segment-shot
		:parameters (?s - step-s ?m - segment ?sc - scale ?ort - orient)
		:precondition ()
		:effect (obs-seg ?s ?m)
		:decomp (:sub-params () :requirements (play-seg ?s ?m))
	)
	
	(:action cam-end-shot
		:parameters (?s - step-s ?sc - scale ?ort - orient)
		:precondition (obs-seg ?s start)
		:effect (obs-seg ?s end) 
		:decomp (:sub-params () :requirements (play-seg ?s end))
	)
	
	(:action cam-shot
		:parameters (?s - step-s ?sc - scale ?ort - orient)
		:precondition (bel (preconds ?s))
		:effect (and (obs ?s) (bel ?s))
		:decomp (:sub-params () :requirements (play ?s ))
	)
	
	(:action virtual-shot-start
		:parameters(?shot-name - virtual-shot-type ?s - step ?p - place)
		:precondition(can-show ?shot-name ?p)
		:effect(obs-seg ?s start)
		:decomp (
		    :sub-params (?at - literal)
			:requirements (and 
				(precond ?s ?at)
				(type ?at at) (arg 1 ?at ?p)
				(play-seg ?s start)
			)
		)
	)

	(:action virtual-shot-end
		:parameters(?shot-name - virtual-shot-type ?s - step ?p - place)
		:precondition(can-show ?shot-name ?p)
		:effect(obs-seg ?s end)
		:decomp (
		    :sub-params (?at - literal)
			:requirements (and
				(effect ?s ?at)
				(type ?at at) (arg 1 ?at ?p)
				(play-seg ?s end)
			)
		)
	)

	(:action virtual-shot-state
		:parameters(?shot-name - virtual-shot-type ?s - step ?obj - movable-thing ?p - place)
		:precondition(and (can-show ?shot-name ?p) (at ?obj ?p))
		:effect(obs (at ?obj ?p))
		:decomp (
		    :sub-params ()
			:requirements (and
				(precond ?s (at ?obj ?p))
				(play-seg ?s very-end)
			)
		)
	)

	(:action cam-act-bridge
		:parameters(?a1 ?a2 - step ?sc - scale ?ort - orient)
		:precondition(and (obs-seg ?a1 start) (bel (preconds ?a1)))
		:effect(and (bel ?a1) (obs-seg ?a2 start))
		:decomp (
			:sub-params (?py ?py2 - play-step ?at - literal ?p - place)
			:requirements (and 
				(= ?py (play-seg ?a1 end))
				(= ?py2	(play-seg ?a2 start))
				(cntg ?py ?py2)
				(type ?at at) (arg 1 ?at ?p)
				(linked-by ?a1 ?a2 ?at)
			)
		)
	)
	
	(:action cam-act-match
		:parameters (?a1 ?a2 ?a3 - step ?o1 ?o2 - orient ?sc - scale)
		:precondition(and (obs-seg ?a1) (not (= ?a1 ?a2)) 
						(not (= ?a2 ?a3)) (not (= ?o1 ?o2)))
		:effect (and (bel ?a2) (bel ?a1) (obs-seg ?a3 start))
		:decomp (
			:sub-params(?c1 ?c2 - step-c)
			:requirements(and
				(not (= ?c1 ?c2)) (cntg ?c1 ?c2)
				(effect ?c1 (obs-seg ?a1 end))
				(effect ?c1 (obs-seg ?a2 start))
				(effect ?c2 (obs-seg ?a2 end))
				(effect ?c2 (obs-seg ?a3 start))
				(has-scale ?c1 ?sc) (has-scale ?c2 ?sc)
				(has-orient ?c1 ?o1) (has-scale ?c2 ?o2)
			)
		)
	)
	
	(:action cont-act
		:parameters (?a - step)
		:precondition (bel (preconds ?a))
		:effect (and (bel ?a) 
				(for-all ?l - literal (effect ?c1 ?l) (bel ?l)) 
				(for-all ?l - literal (effect ?c2 ?l) (bel ?l))
				)
		:decomp (
			:sub-params (?c1 ?c2 - step)
			:requirements (and
				(not (= ?c1 ?c2)) (cntg ?c1 ?c2)
				(linked-by ?c1 ?c2 (obs ?a start))
			)
		)
	)

    (:action arrive
        :parameters (?c1 ?c2 - person ?p0 ?p1 ?p2 ?p3 ?p4 - place ?final-dist - distance)
		:precondition (and (at ?c1 ?p0) (at ?c2 ?p4) (not (= ?c1 ?c2))
			(not (= ?p0 ?p1)) (not (= ?p2 ?p1))(not (= ?p2 ?p3)) (not (= ?p3 ?p4))
			(less-than (distance-between ?p2 ?p3) ?final-dist)
			(less-than (distance-between ?p1 ?p4) (distance-between ?p2 ?p3) )
		)
        :effect(and (at ?c1 ?p2) (at ?c2 ?p3) (facing ?c1 ?c2) (facing ?c2 ?c1))
		
		:decomp(
			:fabula-params (?n0 ?n1 ?n2 ?t1 ?t2 ?call - step-s)
			:fabula-requirements( and
				(not (= ?n0 ?n1)) (not (= ?n1 ?n2)) (not (= ?t1 ?t2))
				(= ?n0 (strut ?c1 ?p0 ?p1))
				(= ?n1 (strut ?c1 ?p1 ?p2))
				(= ?call (call ?c1))
				(= ?n2 (run ?c2 ?p4 ?p3))
				(= ?t1 (turn-to ?c1 ?c2))
				(= ?t2 (turn-to ?c2 ?c1))
				(linked-by ?n0 ?n1 (at ?c1 ?p1))
				(linked-by ?n1 ?t1 (at ?c1 ?p2))
				(linked-by ?n2 ?t2 (at ?c2 ?p3))
				(< ?n0 ?call) (< ?call ?n2))
			:discourse-params (?est ?first-walk ?second-walk ?show-call ?show-run ?end-master - step-d)
			:discourse-requirements( and
				(not (= ?est ?first-walk)) (not (= ?first-walk ?second-walk)) 
				(not (= ?show-call ?show-run)) (not (= ?est ?show-run)) 
				(type ?est cam-segment-shot) (has-scale ?est ewide) (arg 0 ?est ?n0) (arg 1 ?est mid)
				(effect ?first-walk (bel ?n0))
				(effect ?second-walk (bel ?n1))
				(effect ?show-run (bel ?n2))
				(effect ?show-call (bel ?call))
				(= ?end-master (virtual-shot scene-master-shot))
				(< ?show-run ?end-master)
				(< ?show-call ?show-run)
				(< ?first-walk ?second-walk)
				(< ?second-walk ?show-call))
			)
	)
	
	(:action arrive2
        :parameters (?c1 ?c2 - person ?p0 ?p1 ?p2 ?p3 ?p4 - place ?final-dist - distance)
		:precondition (and (at ?c1 ?p0) (at ?c2 ?p4) (not (= ?c1 ?c2))
			(not (= ?p0 ?p1)) (not (= ?p2 ?p1))(not (= ?p2 ?p3)) (not (= ?p3 ?p4))
			(less-than (distance-between ?p2 ?p3) ?final-dist)
			(less-than (distance-between ?p1 ?p4) (distance-between ?p2 ?p3) )
		)
        :effect(and (at ?c1 ?p2) (at ?c2 ?p3) (facing ?c1 ?c2) (facing ?c2 ?c1))
		
		:decomp(
			:fabula-params (?n0 ?n1 ?n2 ?t1 ?t2 ?call - step-s)
			:fabula-requirements( and
				(not (= ?n0 ?n1)) (not (= ?n1 ?n2)) (not (= ?t1 ?t2))
				(= ?n0 (strut ?c1 ?p0 ?p1))
				(= ?n1 (strut ?c1 ?p1 ?p2))
				(= ?call (call ?c1))
				(= ?n2 (run ?c2 ?p4 ?p3))
				(= ?t1 (turn-to ?c1 ?c2))
				(= ?t2 (turn-to ?c2 ?c1))
				(linked-by ?n0 ?n1 (at ?c1 ?p1))
				(linked-by ?n1 ?t1 (at ?c1 ?p2))
				(linked-by ?n2 ?t2 (at ?c2 ?p3))
				(< ?n0 ?call) (< ?call ?n2))
			:discourse-params (?est ?sequence ?end-master - step-d)
			:discourse-requirements( and
				(not (= ?est ?sequence)) 
				(type ?est cam-segment-shot) (has-scale ?est ewide) (arg 0 ?est ?n0) (arg 1 ?est mid)
				(effect ?sequence(bel ?n0))
				(effect ?sequence (bel ?n1))
				(effect ?sequence (bel ?n2))
				(effect ?sequence (bel ?call))
				(< ?est ?sequence) (< ?sequence ?end-master)
				(= ?end-master (virtual-shot scene-master-shot))
			)
	    )
    )

)