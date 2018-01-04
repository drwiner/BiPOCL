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
		virtual-shot-cam - object
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
		(can-show ?cam - virtual-shot-cam ?p - place)
		(bel ?p - plan-elmnt)
        )

    (:decomp-predicates
        (arg ?i - integer ?s - plan-elmnt ?o - object)
		(linked-by ?s ?t - step ?l - literal)
		(< ?s1 ?s2 - step)
		(has-scale ?s - step-c ?sc - scale)
		(has-angle ?s - step-c ?a - angle)
		(has-orient ?s - step ?ort - orient)
		(type ?s - step ?t - operator-type)
		(effect ?s - step ?l - literal)
		(precond ?s - step ?l - literal)
		(cntg ?d1 ?d2 - step-d)
		(truth ?l - literal ?j - bool)
	)
                    
    (:action strut
        :type step-s
        :parameters (?c - person ?p1 ?p2 - place)
        :precondition (and (at ?c ?p1) (not (= ?p1 ?p2)) )
        :effect(and (not (at ?c ?p1)) (at ?c ?p2))
    )

    (:action cam-shot
        :type step-c
        :parameters(?s - step-s ?v - virtual-shot-cam)
        :precondition()
        :effect()
    )

	(:action virtual-step-shot
	    :type step-d
		:parameters(?shot-name - virtual-shot-cam ?s - step-s ?p - place ?at - literal)
		:precondition(and (can-show ?shot-name ?p) )
		:effect(bel ?s)
		:decomp (
		    :fabula-params ()
	        :fabula-requirements(and
				(precond ?s ?at)
				(type ?at at)
				(arg 1 ?at ?p)
			)
	        :discourse-params (?c - step-c)
	        :discourse-requirements(and
	            (= ?c (cam-shot ?s ?shot-name))
	        )
		)
	)

	(:action convey-state
	    :type step-d
	    :parameters(?state - literal)
	    :precondition()
	    :effect (and (bel ?state))
	    :decomp(
	        :fabula-params (?s - step-s)
	        :fabula-requirements(effect ?s ?state)
	        :discourse-params (?c - step-d)
	        :discourse-requirements(and
	            (effect ?c (bel ?s))
	            (truth ?state 1)
	        )
	    )
	)


)