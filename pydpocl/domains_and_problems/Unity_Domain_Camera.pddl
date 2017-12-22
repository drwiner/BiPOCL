(define (domain unity-simple-domain)

    (:types   s-elmnt plan-elmnt cam-param integer - object
		step literal - plan-elmnt
		step-s step-d - step
		step-c - step-d
		operator-type - plan-elmnt
		movable-thing - s-elmnt
		place - s-elmnt
		person thing - movable-thing
		segment - object
		virtual-shot-type - object
		scale fov angle orient - cam-param
		)
		
	(:constants
		start mid end - segment
		low eye high - angle
		cu full wide - scale
		front behind-right - orient
		0 1 - integer
	)

    (:predicates
		(has ?c - person ?t - thing)
        (at ?thing - movable-thing ?place - place)
        (= ?o1 ?o2 - object)
		(facing ?c1 ?c2 - person)
		(arg ?i - integer ?s - plan-elmnt ?o - object)
		(can-show ?cam - virtual-shot-cam ?p - place)
		(bel ?p - plan-elmnt)
		(bel-alu ?p - plan-elmnt)
		(obs-alu ?p - plan-elmnt)
		(obs-seg-alu ?s - step ?m - segment)
		(obs-seg ?s - step ?m - segment)
		(obs ?p - plan-elmnt)
		(obs-seg-cntg ?s - step ?m - segment)
		(play ?s - step-s)
		(play-seg ?s - step-s ?m - segment)
        )

    (:decomp-predicates
		(linked-by ?s ?t - step ?l - literal)
		(< ?s1 ?s2 - step)
		(has-scale ?s - step-c ?sc - scale)
		(has-angle ?s - step-c ?a - angle)
		(has-orient ?s - step ?ort - orient)
		(type ?s - step ?t - operator-type)
		(effect ?s - step ?l - literal)
		(precond ?s - step ?l - literal)
		(cntg ?d1 ?d2 - step-d)
	)
                    
    (:action strut
        :type step-s
        :parameters (?c - person ?p1 ?p2 - place)
        :precondition (and (at ?c ?p1) (not (= ?p1 ?p2)) )
        :effect(and (not (at ?c ?p1)) (at ?c ?p2))
    )

	(:action turn-to
	    :type step-s
		:parameters (?c - person ?c2 - person)
		:precondition (and (not (= ?c ?c2)))
		:effect (facing ?c ?c2)
	)


	(:action cam-start-shot
	    :type step-c
		:parameters (?s - step-s ?sc - scale ?ort - orient)
		:precondition (bel (preconds ?s))
		:effect (and (obs-seg ?s end) (play-seg ?s end) (bel ?s))
	)
	
	(:action cam-step-shot
	    :type step-c
		:parameters (?s - step-s ?m - segment ?sc - scale ?ort - orient)
		:precondition ()
		:effect (and (bel ?s) (play ?s))
	)

	(:action cam-mid-shot
	    :type step-c
		:parameters (?s - step-s ?sc - scale ?ort - orient)
		:precondition (obs-seg ?s start)
		:effect (and (obs-seg ?s mid) (play-seg ?s mid))
	)
	
	(:action cam-end-shot
	    :type step-c
		:parameters (?s - step-s ?sc - scale ?ort - orient)
		:precondition (obs-seg ?s start)
		:effect (and (obs-seg ?s end) (play-seg ?s end))
	)

	(:action convey-state
	    :type step-d
	    :parameters(?state - literal)
	    :precondition()
	    :effect (and (bel ?state))
	    :decomp(
	        :fabula-params (?s - step-s)
	        :fabula-requirements(effect ?s ?state)
	        :discourse-params (?c - step-c)
	        :discourse-requirements(effect ?c (bel ?s))
	    )
	)



)