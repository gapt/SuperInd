/*
 *  loop.h
 *  
 *
 *  Created by Abdelkader kersani on 22/05/12.
 *  Copyright 2012 LIG-CNRS. All rights reserved.
 *
 */
#ifndef TP_LOOP_H

#include "search-structures.h"



#include "../ladr/literals.h"
#include "../ladr/attrib.h"
#include "../ladr/formula.h"
#include "../ladr/maximal.h"

BOOL generates(int I, Plist Si, Plist Sij);



Topform find_notsubsumedcl(Plist Si, Plist Sij, int J);

Topform find_notequalcl(Plist Si, Plist Sij, int J);

Plist look_by_rank(Plist g, int I);

Plist look_by_rank2(Plist g, int I, BOOL index_flat);

Plist get_empty_clauses(Plist g, int I, int IJ);

//BOOL fixed_point(int I, int J, Plist Si, Plist Sij, Plist EmptyCl);

//BOOL fixed_point_alg(int I, int J, Clist sos, Clist usable, Plist EmptyCl);

//BOOL fixed_point_without_empties(int I, int J, Clist sos, Clist usable);

Plist level_empty_clause(Plist g, int I, int J);

Plist level_empty_clause2(Plist g, int I, int J);

Topform plist_member_clause_shift(Plist lst, void *u);

int compute_rank_max(BOOL* tab);
void init_tab_rank(BOOL* tab);

#endif