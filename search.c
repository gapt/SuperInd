static
void index_and_process_initial_clauses(void)
	{
		Clist_pos p;
		Clist temp_sos;
		/******************************* Modif ******/
		Glob.ind_empty_clause = FALSE; // No inductive clause is generated yet
		/****************************/
		// Index Usable clauses if hyper, UR, or binary-res are set.
		
		Glob.use_clash_idx = (flag(Opt->binary_resolution) ||
							  flag(Opt->neg_binary_resolution) ||
							  flag(Opt->pos_hyper_resolution) ||
							  flag(Opt->neg_hyper_resolution) ||
							  flag(Opt->pos_ur_resolution) ||
							  flag(Opt->neg_ur_resolution));
		
		// Allocate and initialize indexes (even if they won't be used).
		
		init_literals_index();  // fsub, bsub, fudel, budel, ucon
		
		init_demodulator_index(DISCRIM_BIND, ORDINARY_UNIF, 0);
		
		init_back_demod_index(FPA, ORDINARY_UNIF, 10);
		
		Glob.clashable_idx = lindex_init(FPA, ORDINARY_UNIF, 10,
										 FPA, ORDINARY_UNIF, 10);
		
		init_hints(ORDINARY_UNIF, Att.bsub_hint_wt,
				   flag(Opt->collect_hint_labels),
				   flag(Opt->back_demod_hints),
				   demodulate_clause);
		init_semantics(Glob.interps, Clocks.semantics,
					   stringparm1(Opt->multiple_interps),
					   parm(Opt->eval_limit),
					   parm(Opt->eval_var_limit));
		
		// Do Sos and Denials last, in case we PROCESS_INITIAL_SOS.
		
		////////////////////////////////////////////////////////////////////////////
		// Usable
		
		for (p = Glob.usable->first; p != NULL; p = p->next) {
			Topform c = p->c;
			//init_ancestors_topform(c);
			assign_clause_id(c);
			mark_maximal_literals(c->literals);
			mark_selected_literals(c->literals, stringparm1(Opt->literal_selection));
			if (flag(Opt->dont_flip_input))
				orient_equalities(c, FALSE);  // mark, but don't allow flips
			else
				c = orient_input_eq(c);  /* this replaces c if any flipping occurs */
			index_literals(c, INSERT, Clocks.index, FALSE);
			index_back_demod(c, INSERT, Clocks.index, flag(Opt->back_demod));
			index_clashable(c, INSERT);
		}
		
		////////////////////////////////////////////////////////////////////////////
		// Demodulators
		
		if (!clist_empty(Glob.demods) && !flag(Opt->eval_rewrite)) {
			fflush(stdout);
			bell(stderr);
			fprintf(stderr,
					"\nWARNING: The use of input demodulators is not well tested\n"
					"and discouraged.  You might need to clear(process_initial_sos)\n"
					"so that sos clauses are not rewritten and deleted.\n");
			fflush(stderr);
		}
		
		for (p = Glob.demods->first; p != NULL; p = p->next) {
			Topform c = p->c;
			assign_clause_id(c);
			if (flag(Opt->eval_rewrite)) {
				if (c->is_formula) {
					/* make it into a pseudo-clause */
					c->literals = new_literal(TRUE, formula_to_term(c->formula));
					upward_clause_links(c);
					zap_formula(c->formula);
					c->formula = NULL;
					c->is_formula = FALSE;
					clause_set_variables(c, MAX_VARS);
					mark_oriented_eq(c->literals->atom);
				}
			}
			else {
				if (!pos_eq_unit(c->literals))
					fatal_error("input demodulator is not equation");
				else {
					int type;
					if (flag(Opt->dont_flip_input))
						orient_equalities(c, FALSE);  /* don't allow flips */
					else
						c = orient_input_eq(c);  /* this replaces c if any flipping occurs */
					if (c->justification->next != NULL) {
						printf("\nNOTE: input demodulator %d has been flipped.\n", c->id);
						fflush(stdout);
						fprintf(stderr, "\nNOTE: input demodulator %d has been flipped.\n",
								c->id);
						if (flag(Opt->bell))
							bell(stderr);
						fflush(stderr);
					}
					type = demodulator_type(c,
											parm(Opt->lex_dep_demod_lim),
											flag(Opt->lex_dep_demod_sane));
					if (flag(Opt->dont_flip_input) &&
						type != ORIENTED &&
						!renamable_flip_eq(c->literals->atom)) {
						type = ORIENTED;  /* let the user beware */
						mark_oriented_eq(c->literals->atom);
						bell(stderr);
						fprintf(stderr,"\nWARNING: demodulator does not satisfy term order\n");
						fflush(stderr);
						printf("\nWARNING: demodulator does not satisfy term order: ");
						f_clause(c);
						fflush(stdout);
					}
					else if (type == NOT_DEMODULATOR) {
						Term a = ARG(c->literals->atom,0);
						Term b = ARG(c->literals->atom,1);
						printf("bad input demodulator: "); f_clause(c);
						if (term_ident(a, b))
							fatal_error("input demodulator is instance of x=x");
						else if (!variables_subset(a, b) && !variables_subset(b, a))
							fatal_error("input demoulator does not have var-subset property");
						else
							fatal_error("input demoulator not allowed");
					}
					index_demodulator(c, type, INSERT, Clocks.index);
				}
			}
		}
		
		if (flag(Opt->eval_rewrite))
			init_dollar_eval(Glob.demods);
		
		////////////////////////////////////////////////////////////////////////////
		// Hints
		
		if (Glob.hints->first) {
			for (p = Glob.hints->first; p != NULL; p = p->next) {
				Topform h = p->c;
				// assign_clause_id(h);  // This should be optional
				orient_equalities(h, TRUE);
				renumber_variables(h, MAX_VARS);
				index_hint(h);
			}
		}
		
		////////////////////////////////////////////////////////////////////////////
		// Sos
		
		// Move Sos to a temporary list, then process that temporary list,
		// putting the clauses back into Sos in the "correct" way, either
		// by calling cl_process() or doing it here.
		
		temp_sos = Glob.sos;                    // move Sos to a temporary list
		name_clist(temp_sos, "temp_sos");       // not really necessary
		Glob.sos = clist_init("sos");           // get a new (empty) Sos list
		
		if (flag(Opt->process_initial_sos)) {
			
			if (flag(Opt->print_initial_clauses))
				printf("\n");
			/*********************************** Modif **************************/
			Topform schema;// the (alpha,C)-clause
			int unit_loop = 0; // unit_loop is the number of (alpha,C)-clauses
			while (temp_sos->first) {
				Topform c = temp_sos->first->c;
				if (!param_free(c)) {//
					unit_loop ++;//
					if (unit_loop == 1) {//
						
						schema = c;//
						printf("Loop1"); p_clause(schema);
					}
				}
				Topform new;
				clist_remove(c, temp_sos);
				clist_append(c, Glob.disabled);
				
				new = copy_inference(c);  // c has no ID, so this is tricky
				cl_process_simplify(new);
				if (new->justification->next == NULL) {
					// No simplification occurred, so make it a clone of the parent.
					zap_just(new->justification);
					new->justification = copy_justification(c->justification);
					// Get all attributes, not just inheritable ones.
					zap_attributes(new->attributes);
					new->attributes = copy_attributes(c->attributes);
				}
				else {
					// Simplification occurs, so make it a child of the parent.
					assign_clause_id(c);
					new->justification->u.id = c->id;
					if (flag(Opt->print_initial_clauses)) {
						printf("           ");
						fwrite_clause(stdout, c, CL_FORM_STD);
					}
				}
				cl_process(new);  // This re-simplifies, but that's ok.
			}
			/********************************* Modif ********************** */
			/* if (unit_loop == 1) {// if there is only one (alpha,c)-clause of the form N(X) | p(X)
			 printf("Loop2"); p_clause(schema);
			 
			 Topform Newc = build_loop_clause(schema);//we add a new clause of the form N(s(X)) | p(X)
			 printf("Loop\n"); 
			 Glob.SI = plist_append(NULL, schema);
			 Glob.SIJ = plist_append(NULL, Newc);
			 Glob.ind_empty_clause = TRUE;
			 
			 }*/
			
			
			// This will put processed clauses back into Sos.
			limbo_process(TRUE);  // back subsumption and back demodulation.
			
		}
		else {
			/* not processing initial sos */
			fflush(stdout);
			bell(stderr);
			fprintf(stderr,
					"\nWARNING: clear(process_initial_sos) is not well tested.\n"
					"We usually recommend against using it.\n");
			fflush(stderr);
			
			/* not applying full processing to initial sos */
			while (temp_sos->first) {
				Topform c = temp_sos->first->c;
				clist_remove(c, temp_sos);
				
				if (number_of_literals(c->literals) == 0)
				/* in case $F is in input, or if predicate elimination finds proof */
					handle_proof_and_maybe_exit(c);
				else {
					assign_clause_id(c);
					if (flag(Opt->dont_flip_input))
						orient_equalities(c, FALSE);
					else
						c = orient_input_eq(c);
					mark_maximal_literals(c->literals);
					mark_selected_literals(c->literals,
										   stringparm1(Opt->literal_selection));
					c->weight = clause_weight(c->literals);
					if (!clist_empty(Glob.hints)) {
						clock_start(Clocks.hints);
						adjust_weight_with_hints(c,
												 flag(Opt->degrade_hints),
												 flag(Opt->breadth_first_hints));
						clock_stop(Clocks.hints);
					}
					
					c->initial = TRUE;
					insert_into_sos2(c, Glob.sos);
					printf("KK");
					//index_literals(c, INSERT, Clocks.index, FALSE);
					index_back_demod(c, INSERT, Clocks.index, flag(Opt->back_demod));
				}
			}
		}
		
		clist_zap(temp_sos);  // free the temporary list
		
		////////////////////////////////////////////////////////////////////////////
		// Print
		
		print_separator(stdout, "end of process initial clauses", TRUE);
		
		print_separator(stdout, "CLAUSES FOR SEARCH", TRUE);
		
		if (flag(Opt->print_initial_clauses)) {
			printf("\n%% Clauses after input processing:\n");
			fwrite_clause_clist(stdout,Glob.usable,  CL_FORM_STD);
			fwrite_clause_clist(stdout,Glob.sos,     CL_FORM_STD);
			fwrite_demod_clist(stdout,Glob.demods,   CL_FORM_STD);
		}
		if (Glob.hints->length > 0) {
			int redundant = redundant_hints();
			printf("\n%% %d hints (%d processed, %d redundant).\n",
				   Glob.hints->length - redundant, Glob.hints->length, redundant);
		}
		
		print_separator(stdout, "end of clauses for search", TRUE);
		
	}  // index_and_process_initial_clauses

