/*
 *  loop.c
 *  
 *
 *  Created by Abdelkader kersani on 22/05/12.
 *  Copyright 2012 LIG-CNRS. All rights reserved.
 *
 */

#include "loop.h"

/*
 return the empty clauses of a rank between I and J i.e J > rank > I
 */
Plist level_empty_clause(Plist g, int I, int J){
	if (isEmpty(g)) {
		fatal_error("level_empty_clause : the list of empty clauses is empty");
	}
	Plist p;
	int rank ;
	Plist res = NULL;
	for (p = g; p; p = p->next){
		rank = get_rank(p->v) ;
		if ( rank >= I && rank < J ) {
			res=plist_prepend(res, p->v);
		}
	}
	return res;

}

/*
 return the empty clauses of a rank between I and J i.e J > rank >= I
 */
Plist level_empty_clause2(Plist g, int I, int J){
	if (isEmpty(g)) {
		fatal_error("level_empty_clause : the list of empty clauses is empty");
	}
	Plist p = g;
	int rank ;
	Ilist Tested_Rank = NULL;
	int R=1;
	Plist res = NULL;
	int dif = J - I;
	while (p && R <= dif){
		rank = get_rank(p->v) ;
		//printf("ecl : ");p_clause(p->v);
		if ( rank > I && rank <= J) { // les clauses vide ]i,i+j]
			if(!ilist_member(Tested_Rank, rank)){
				res=plist_append(res, p->v);
				//printf("res : ");p_plist(res);
				Tested_Rank = ilist_append(Tested_Rank, rank);
				//printf("TR : ");p_ilist(Tested_Rank);
				R++;
				//printf("R = %d",R);
			}
		}
		p=p->next;
	}
	//printf("res1 : ");p_plist(res);
	return res;
	
}
/**/
// returns true if the parents of Ci are in Si or they are of rank I and their parents are in Si
BOOL parents_in_Si(Plist Si, Topform Ci, int I){
	Topform c;
	Ilist p;
	BOOL res = TRUE;
	Ilist parents = get_parents(Ci->justification, TRUE);
	//printf("TT ");p_ilist(parents);printf(" TT "); p_clause(Ci);
	for (p = parents; p; p = p->next) {
		//printf("S %d ", p);
		c = find_clause_by_id(p->i);
		//printf("DDD");
		//p_clause(c);
		if (!plist_member_clause(Si, c) && !bottom_clause(c) ) {
			if(get_rank(c) < I){
				/*printf(" parents not in Si : ");p_clause(c);
				p_plist(Si);
				printf(" la clause en question ");p_clause(Ci);*/
				return FALSE;
			}
			else {
				if (get_rank(c)==I) {
					//printf("==");
					res = parents_in_Si(Si,c,I) ;
					if (!res) {
						return res;
					}
				}
				//else {
				//	fatal_error("the rank of the parent is lower than the child");
				//}

				
			}
		}
		

		
	}
	//printf("PPP");
	return res;
}
/*
 Check whether Si generates Sij
 
 
 
 */
BOOL generates(int I, Plist Si, Plist Sij){
	//p_plist(Si);
	//p_plist(Sij);
	if(isEmpty(Si)){
		return FALSE;
		
	}
	if(isEmpty(Sij)) {
		return TRUE;
	}
	Plist p, ancestor, tmp;
	//Topform c;
	for (p = Sij; p; p = p->next) {// for each clause of Sij
		//p_clause(p->v);
		//printf("I = %d", I);
		//ancestor = hh(p->v, I);

		ancestor = get_clause_ancestors_ofrank(p->v, I); // we look for all its ancestors of rank I
		//c=(Topform)p->v;
		//ancestor = get_clanc_rank(c->id, NULL, I);
		//printf("A");p_plist(ancestor);
		if(isEmpty(ancestor)){// if there is no ancestors of rank I that means the class is not admissible
			/*printf("the clause : ");
			p_clause(p->v);
			printf(" has as ancestors :  ");
			Plist ancetre = get_clause_ancestors(p->v);
			p_plist(ancetre);
			p_plist(ancestor);*/
			return FALSE;
			//fatal_error("not admissible class");
		}
		for (tmp = ancestor; tmp; tmp = tmp->next) {// for each ancestor 
			if(!plist_member_clause(Si, tmp->v) && !(bottom_clause(tmp->v)) ){
				/*printf(" \n Si : \n ");
				//p_plist(Si);
				printf("is a bottom clause = %d \n", bottom_clause(tmp->v));
				printf("the problem clause : ");p_clause(tmp->v);
				printf("rank of the ancestor = %d \n" ,  get_rank(tmp->v));*/
				return FALSE;
			}
			
		}
		//free_plist(ancestor);
		
	}
	//printf("C");
	return TRUE;
}

/*
 Check whether Si generates Sij
 
 
 
 */
BOOL generates1(int I, Plist Si, Plist Sij){
	//p_plist(Si);
	//p_plist(Sij);
	int comp=0;
	if(isEmpty(Si)){
		return FALSE;
		
	}
	if(isEmpty(Sij)) {
		return TRUE;
	}
	Plist p, ancestor, tmp;
	//Topform c;
	for (p = Sij; p; p = p->next) {// for each clause of Sij
		//p_clause(p->v);
		//printf("I = %d", I);
		//ancestor = hh(p->v, I);
		
		ancestor = get_clause_ancestors_ofrank(p->v, I); // we look for all its ancestors of rank I
		//c=(Topform)p->v;
		//ancestor = get_clanc_rank(c->id, NULL, I);
		//printf("A");p_clause(p->v);
		//printf("X : %d ", comp);
		//comp++;
		if(isEmpty(ancestor)){// if there is no ancestors of rank I that means the class is not admissible
			/*printf("the clause : ");
			 p_clause(p->v);
			 printf(" has as ancestors :  ");
			 Plist ancetre = get_clause_ancestors(p->v);
			 p_plist(ancetre);
			 p_plist(ancestor);
			//fatal_error("not admissible class2");*/
			return FALSE;
		}
		//printf("A");p_clause(p->v);
		for (tmp = ancestor; tmp; tmp = tmp->next) {// for each ancestor 
			//printf("B");
			if(!plist_member_clause(Si, tmp->v)){ 
				//printf("C");
				//printf("CL is not in Si = %d", plist_member_clause(Si, tmp->v));
				
				//p_clause(tmp->v);
				//printf("D");
				if(!(bottom_clause(tmp->v))) {
					
					//printf("parents : %d ",parents_in_Si(Si,tmp->v,I) );
					if (!parents_in_Si(Si,tmp->v,I)) {
						/*printf(" \n Si : \n ");
						//p_plist(Si);
						printf("is a bottom clause = %d \n", bottom_clause(tmp->v));
						printf("the problem clause : ");p_clause(tmp->v);
						printf("rank of the ancestor = %d \n" ,  get_rank(tmp->v));*/
						return FALSE;
					}
					//printf("A");
				}
			}
			
		}
		//free_plist(ancestor);
		
	}
	//printf("C");
	return TRUE;
}

/*
 
 retourne une clause C de Si telle que shift(C) n'est pas subsumée par aucune clause de Sij.
 
 */
Topform find_notsubsumedcl(Plist Si, Plist Sij, int J){
	Plist  p, anc, tmp;
	BOOL state=TRUE;
	for (p = Si; p; p = p->next) {/*for each clause of Si */
		state = TRUE;
		
		Topform cij = shift_cl(p->v, J);/*compute its shift clause*/
		//printf("r1\n"); printf(" J = %d ", J) ;p_clause(cij); printf("r1\n");
		int n=0;
		for (tmp = Sij; tmp; tmp = tmp->next) { /*for each clause de Sij*/
			//printf("n = %d ", n);p_clause(tmp->v);
			if(state){
				//
				Topform top=tmp->v;
				//printf("r0\n");p_clause(cij); printf("r0\n");
				//printf("r1\n");p_clause(top); printf("r1\n");
			
				if(subsumes_param(tmp->v, cij)){//if its shift occurs in Sij then it's subsumed 
					//printf("kk");
					state = FALSE;
					//return NULL;
				}
			}
			
		}
		if (state) {
			return p->v;
		}
	}
	return NULL;
}
/*
 
 retourne une clause C de Si telle que shift(C) n'est pas égal à aucune clause de Sij.
 
 */
Topform find_notequalcl(Plist Si, Plist Sij, int J){
	Plist  p, anc, tmp;
	BOOL state=TRUE;
	for (p = Si; p; p = p->next) {/*for each clause of Si */
		state = TRUE;
		
		Topform cij = shift_cl(p->v, J);/*compute its shift clause*/
		/*printf("r1\n");p_clause(cij); printf("r1\n");
		printf("K\n");p_clause(cij);printf("K\n");*/
		int n=0;
		for (tmp = Sij; tmp; tmp = tmp->next) { /*for each clause de Sij*/
			//printf("n = %d ", n);p_clause(tmp->v);
			if(state){
				//if(subsumes_param(tmp->v, cij)){
				Topform top=tmp->v;
				//printf("r0\n");p_clause(cij); printf("r0\n");
				//printf("r1\n");p_clause(top); printf("r1\n");
				
				if(clause_ident_order(top,cij)){//if its shift occurs in Sij then it's subsumed 
					//printf("kk");
					state = FALSE;
					//return NULL;
				}
			}
			
		}
		if (state) {
			return p->v;
		}
	}
	return NULL;
}
/*
  
 
 
 
 
 

BOOL parent_emptycl(Topform Ci){
	Plist anc=get_clause_ancestors_ofrank(C, I);
	
}*/

/*
 retourne toutes les clause de g de rang I
 */
Plist look_by_rank(Plist g, int I){
	Plist p, res;
	res=NULL;
	for (p = g; p; p = p->next) {
		if((get_rank(p->v) == I) && get_var_term(p->v))
			res=plist_prepend(res, p->v);
	}
	return res;
}
/*
 Return all the clauses of g of rank I 
 the clauses are Si-flat if index_flat is true
 */
Plist look_by_rank2(Plist g, int I, BOOL index_flat){
	Plist p, res;
	res=NULL;
	for (p = g; p; p = p->next) {
		if((get_rank(p->v) == I) && get_var_term(p->v)){
			if (index_flat) {
				if (iflat(I,p->v)) {
					res=plist_prepend(res, p->v);
				}
			}
			else {
				res=plist_prepend(res, p->v);
			}

			
			
		}
	}
	return res;
}
BOOL is_ancestor(int I,Topform Ci, Topform Cij){
	Plist ancestors = get_clause_ancestors_ofrank(Cij, I); 
	return plist_member_clause(ancestors, Ci);
}
/*
 retourne toutes les clauses 
 */
Plist get_empty_clauses(Plist g, int I, int IJ){
	Plist p, res;
	res=NULL;
	int rank;
	for (p = g; p; p = p->next) {
		rank =get_rank(p->v);
		if(rank < IJ && rank >= I )
			if (pureparam_cst_topform(p->v)) {
				
				res=plist_prepend(res, p->v);
			}
		/*else {
			fatal_error("get_empty_clauses : it's not an empty clause");
		}*/

			
	}
	//printf("res : ");
	//p_plist(res);
	return res;
}
/* PUBLIC */
/* Return u if a Plist lst contains a topform u and  else return NULL*/ 
Topform plist_member_clause_shift(Plist lst, void *u)
{
	if (lst == NULL)
		return NULL;
	else{ 
		Topform v1 =lst->v;
		Topform v2 = (Topform)u;
		/*if(get_rank(v1) == 1){
		 printf("Begin");
		 p_clause(v2);
		 p_clause(v1);
		 }*/
		if (clause_ident_order(v1, v2)){
			//printf(" egal ");
			
			return v1;
		}
		else{
			//printf(" pasegal ");
			
			return plist_member_clause_shift(lst->next, v2);
		}
	}
}  /* plist_member_clause */

/*
 Check whether 
 
 
 
 
 */

int compute_rank_max(BOOL* tab){
	int res = 0;
	while (res <= 40 && tab[res]) {
		res++;
		
	}
	return res - 1;
	
}
void init_tab_rank(BOOL* tab){
	int res = 1;
	while (res <= 40 ) {
		tab[res]=FALSE;
		res++;
		
	}
}


