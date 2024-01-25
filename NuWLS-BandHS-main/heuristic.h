#ifndef _HEURISTIC_H_
#define _HEURISTIC_H_

#include "basis_pms.h"
#include "deci.h"

void ISDist::init(vector<int> &init_solution)
{
    local_times = 0;
    local_times_hard = 0;
    if_exceed = 0;
    soft_large_weight_clauses_count = 0;

    for (int c = 0; c < num_clauses; c++)
    {
        selected_times[c] = 0;
        clause_score[c] = 1;
    }

    for (int v = 1; v < num_vars; v++){
        lit_score[v] = 1; //positive lit
        lit_score[v+num_vars] = 1; //negative lit
        lit_times[v] = 0;
        lit_times[v+num_vars] = 0;
    }

    if (1 == problem_weighted) // weighted partial MaxSAT
    {
        if (0 != num_hclauses)
        {
            if ((0 == local_soln_feasible || 0 == best_soln_feasible))
            {
                for (int c = 0; c < num_clauses; c++)
                {
                    already_in_soft_large_weight_stack[c] = 0;
                    clause_selected_count[c] = 0;
                    clause_weight[c] = 1;
                }
            }
            else
            {
                for (int c = 0; c < num_clauses; c++)
                {
                    already_in_soft_large_weight_stack[c] = 0;
                    clause_selected_count[c] = 0;

                    if (org_clause_weight[c] == top_clause_weight)
                        clause_weight[c] = 1;
                    else
                    {
                        clause_weight[c] = tuned_org_clause_weight[c];
                        if (clause_weight[c] > s_inc && already_in_soft_large_weight_stack[c] == 0)
                        {
                            already_in_soft_large_weight_stack[c] = 1;
                            soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
                        }
                    }
                }
            }
        }
        else
        {
            for (int c = 0; c < num_clauses; c++)
            {
                already_in_soft_large_weight_stack[c] = 0;
                clause_selected_count[c] = 0;
                clause_weight[c] = tuned_org_clause_weight[c];
                if (clause_weight[c] > s_inc && already_in_soft_large_weight_stack[c] == 0)
                {
                    already_in_soft_large_weight_stack[c] = 1;
                    soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
                }
            }
        }
    }
    else // unweighted partial MaxSAT
    {
        for (int c = 0; c < num_clauses; c++)
        {
            already_in_soft_large_weight_stack[c] = 0;
            clause_selected_count[c] = 0;

            if (org_clause_weight[c] == top_clause_weight)
                clause_weight[c] = 1;
            else
            {
                if ((0 == local_soln_feasible || 0 == best_soln_feasible) && num_hclauses > 0)
                {
                    clause_weight[c] = 1;
                }
                else
                {
                    clause_weight[c] = coe_soft_clause_weight;
                    if (clause_weight[c] > 1 && already_in_soft_large_weight_stack[c] == 0)
                    {
                        already_in_soft_large_weight_stack[c] = 1;
                        soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
                    }
                }
            }
        }
    }

    if (init_solution.size() == 0)
    {
        for (int v = 1; v <= num_vars; v++)
        {
            cur_soln[v] = rand() % 2;
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }
    else
    {
        for (int v = 1; v <= num_vars; v++)
        {
            cur_soln[v] = init_solution[v];
            if (cur_soln[v] != 0 && cur_soln[v] != 1)
                cur_soln[v] = rand() % 2;
            time_stamp[v] = 0;
            unsat_app_count[v] = 0;
        }
    }
    local_soln_feasible = 0;
    // init stacks
    hard_unsat_nb = 0;
    soft_unsat_weight = 0;
    hardunsat_stack_fill_pointer = 0;
    softunsat_stack_fill_pointer = 0;
    unsatvar_stack_fill_pointer = 0;
    large_weight_clauses_count = 0;

    /* figure out sat_count, sat_var and init unsat_stack */
    for (int c = 0; c < num_clauses; ++c)
    {
        sat_count[c] = 0;
        for (int j = 0; j < clause_lit_count[c]; ++j)
        {
            if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
            {
                sat_count[c]++;
                sat_var[c] = clause_lit[c][j].var_num;
            }
        }
        if (sat_count[c] == 0)
        {
            unsat(c);
        }
    }

    /*figure out score*/
    for (int v = 1; v <= num_vars; v++)
    {
        score[v] = 0.0;
        for (int i = 0; i < var_lit_count[v]; ++i)
        {
            int c = var_lit[v][i].clause_num;
            if (sat_count[c] == 0)
                score[v] += clause_weight[c];
            else if (sat_count[c] == 1 && var_lit[v][i].sense == cur_soln[v])
                score[v] -= clause_weight[c];
        }
    }

    // init goodvars stack
    goodvar_stack_fill_pointer = 0;
    for (int v = 1; v <= num_vars; v++)
    {
        if (score[v] > 0)
        {
            already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
            mypush(v, goodvar_stack);
        }
        else
            already_in_goodvar_stack[v] = -1;
    }
}

int ISDist::pick_var()
{
    int i, v;
    int best_var;
    int sel_c;
    lit *p;

    if (goodvar_stack_fill_pointer > 0)
    {
        int best_array_count = 0;
        if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob)
            return goodvar_stack[rand() % goodvar_stack_fill_pointer];

        if (goodvar_stack_fill_pointer < hd_count_threshold)
        {
            best_var = goodvar_stack[0];

            for (i = 1; i < goodvar_stack_fill_pointer; ++i)
            {
                v = goodvar_stack[i];
                if (score[v] > score[best_var])
                {
                    best_var = v;
                }
                else if (score[v] == score[best_var])
                {
                    if (time_stamp[v] < time_stamp[best_var])
                    {
                        best_var = v;
                    }
                }
            }
            return best_var; // best_array[rand() % best_array_count];
        }
        else
        {
            best_var = goodvar_stack[rand() % goodvar_stack_fill_pointer];

            for (i = 1; i < hd_count_threshold; ++i)
            {
                v = goodvar_stack[rand() % goodvar_stack_fill_pointer];
                if (score[v] > score[best_var])
                {
                    best_var = v;
                }
                else if (score[v] == score[best_var])
                {
                    if (time_stamp[v] < time_stamp[best_var])
                    {
                        best_var = v;
                    }
                }
            }
            return best_var; // best_array[rand() % best_array_count];
        }
    }

    update_clause_weights();

    if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob){
        if (hardunsat_stack_fill_pointer > 0)
            sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
        else{
            while(1){
                sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
                if (clause_lit_count[sel_c] != 0)
                    break;
            }
        }
        return clause_lit[sel_c][rand() % clause_lit_count[sel_c]].var_num;
    }

    int sense, c;
    int best_lit;
    
    if (hardunsat_stack_fill_pointer > 0)
    {
        if (best_soln_feasible > 0)
            sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
        else{
            double max = -10000000000, ucb;
            c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
            for (int j = 0; j < clause_lit_count[c]; j++){
                v = clause_lit[c][j].var_num;
                sense = clause_lit[c][j].sense;
                ucb = lit_score[v + (1 - sense) * num_vars] + lambda_hard * sqrt((log(local_times_hard + 1)) / ((double)(lit_times[v + (1 - sense) * num_vars] + 1)));
                if (ucb > max){
                    max = ucb;
                    best_lit = v + (1 - sense) * num_vars;
                    best_var = v;
                }
                else if (ucb == max){
                    if (score[v] > score[best_var]){
                        best_lit = v + (1 - sense) * num_vars;
                        best_var = v;
                    }
                    else if (score[v] == score[best_var]){
                        if (time_stamp[v] < time_stamp[best_var]){
                            best_lit = v + (1 - sense) * num_vars;
                            best_var = v;
                        }
                    }
                }
            }
            lit_times[best_lit]++;
            selected_lits[local_times_hard % backward_step_hard] = best_lit;
            if (local_times_hard > 0)
            {
                long long s = pre_unsat_hard_nb - hard_unsat_nb;
                if (s != 0)
                    update_lit_scores(s);
            }
            pre_unsat_hard_nb = hard_unsat_nb;
            local_times_hard++;
            return best_var;
        }
    }
    else{
        double max = -10000000000, ucb;
        for (int i = 0; i < ArmNum; i++){
            while(1)
            {
                sampled_clauses[i] = softunsat_stack[rand() % softunsat_stack_fill_pointer];
                if (clause_lit_count[sampled_clauses[i]] != 0)
                    break;
            }
            ucb = clause_score[sampled_clauses[i]] + lambda * sqrt((log(local_times + 1)) / ((double)(selected_times[sampled_clauses[i]] + 1)));
            if (ucb > max){
                max = ucb;
                sel_c = sampled_clauses[i];
            }
        }
        selected_times[sel_c]++;
        selected_clauses[local_times % backward_step] = sel_c;
        if (local_times > 0)
        {
            long long s = pre_unsat_weight - soft_unsat_weight;
            if (s != 0)
                update_clause_scores(s);
        }
        pre_unsat_weight = soft_unsat_weight;
        local_times++;
    }
    
    best_var = clause_lit[sel_c][0].var_num;
    p = clause_lit[sel_c];
    for (p++; (v = p->var_num) != 0; p++)
    {
        if (score[v] > score[best_var])
            best_var = v;
        else if (score[v] == score[best_var])
        {
            if (time_stamp[v] < time_stamp[best_var])
                best_var = v;
        }
    }

    return best_var;
}

void ISDist::local_search_with_decimation(char *inputfile)
{
    if (1 == problem_weighted)
    {
        if (total_soft_length / num_sclauses > 100)
        {
            //cout << "c avg_soft_length: " << total_soft_length / num_sclauses << endl;
            h_inc = 300;
            s_inc = 100;
        }
        if (0 != num_hclauses)
        {
            coe_tuned_weight = (double)(coe_soft_clause_weight * num_sclauses) / double(total_soft_weight);
            for (int c = 0; c < num_clauses; c++)
            {
                if (org_clause_weight[c] != top_clause_weight)
                {
                    tuned_org_clause_weight[c] = (double)org_clause_weight[c] * coe_tuned_weight;
                }
            }
        }
        else
        {
            softclause_weight_threshold = 0;
            soft_smooth_probability = 1E-3;
            hd_count_threshold = 22;
            rdprob = 0.036;
            rwprob = 0.48;
            s_inc = 1.0;
            for (int c = 0; c < num_clauses; c++)
            {
                tuned_org_clause_weight[c] = org_clause_weight[c];
            }
        }
    }
    else
    {
        if (0 == num_hclauses)
        {
            hd_count_threshold = 94;
            coe_soft_clause_weight = 397;
            rdprob = 0.007;
            rwprob = 0.047;
            soft_smooth_probability = 0.002;
            softclause_weight_threshold = 550;
        }
    }
    Decimation deci(var_lit, var_lit_count, clause_lit, org_clause_weight, top_clause_weight);
    deci.make_space(num_clauses, num_vars);
    //total_step = 0;
    opt_unsat_weight = __LONG_LONG_MAX__;
    for (tries = 1; tries < max_tries; ++tries)
    {
        deci.init(local_opt_soln, best_soln, unit_clause, unit_clause_count, clause_lit_count);
        deci.unit_prosess();
        init(deci.fix);

        if (get_runtime()>=cutoff_time)
            return;

        long long local_opt = __LONG_LONG_MAX__;
        max_flips = max_non_improve_flip;
        for (step = 1; step < max_flips; ++step)
        {
            if (hard_unsat_nb == 0)
            {
                local_soln_feasible = 1;
                if (local_opt > soft_unsat_weight)
                {
                    local_opt = soft_unsat_weight;
                    max_flips = step + max_non_improve_flip;
                }
                if (soft_unsat_weight < opt_unsat_weight)
                {
                    opt_time = get_runtime();
                    //cout << "o " << soft_unsat_weight << " " << total_step << " " << tries << " " << soft_smooth_probability << " " << opt_time << endl;
                    cout << "o " << soft_unsat_weight << " " << opt_time << endl;
                    opt_unsat_weight = soft_unsat_weight;
                    for (int v = 1; v <= num_vars; ++v)
                        best_soln[v] = cur_soln[v];
                    if (opt_unsat_weight <= best_known)
                    {
                        cout << "c best solution found." << endl;
                        if (opt_unsat_weight < best_known)
                        {
                            cout << "c a better solution " << opt_unsat_weight << endl;
                        }
                        return;
                    }
                }
                if (best_soln_feasible == 0)
                {
                    best_soln_feasible = 1;
                    // break;
                }
            }
            // if(goodvar_stack_fill_pointer==0) cout<<step<<": 0"<<endl;
            if (step % 1000 == 0)
            {
                double elapse_time = get_runtime();
                if (elapse_time >= cutoff_time)
                    return;
                else if (opt_unsat_weight == 0)
                    return;
            }
            int flipvar = pick_var();
            flip(flipvar);
            time_stamp[flipvar] = step;
            //total_step++;
        }
        if (get_runtime()>=cutoff_time)
            return;
    }
}

void ISDist::hard_increase_weights()
{
    int i, c, v;
    for (i = 0; i < hardunsat_stack_fill_pointer; ++i)
    {
        c = hardunsat_stack[i];
        clause_weight[c] += h_inc;

        if (clause_weight[c] == (h_inc + 1))
            large_weight_clauses[large_weight_clauses_count++] = c;

        for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
        {
            score[v] += h_inc;
            if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
            {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v, goodvar_stack);
            }
        }
    }
    return;
}

void ISDist::soft_increase_weights()
{
    int i, c, v;

    if (1 == problem_weighted)
    {
        for (i = 0; i < softunsat_stack_fill_pointer; ++i)
        {
            c = softunsat_stack[i];
            if (clause_lit_count[c] == 0)  continue;
            if (clause_weight[c] >= tuned_org_clause_weight[c] + softclause_weight_threshold)
                continue;
            else
                clause_weight[c] += s_inc;

            if (clause_weight[c] > s_inc && already_in_soft_large_weight_stack[c] == 0)
            {
                already_in_soft_large_weight_stack[c] = 1;
                soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
            }
            for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
            {
                score[v] += s_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    else
    {
        for (i = 0; i < softunsat_stack_fill_pointer; ++i)
        {
            c = softunsat_stack[i];
            if (clause_lit_count[c] == 0)  continue;
            if (clause_weight[c] >= coe_soft_clause_weight + softclause_weight_threshold)
                continue;
            else
                clause_weight[c] += s_inc;

            if (clause_weight[c] > s_inc && already_in_soft_large_weight_stack[c] == 0)
            {
                already_in_soft_large_weight_stack[c] = 1;
                soft_large_weight_clauses[soft_large_weight_clauses_count++] = c;
            }
            for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
            {
                score[v] += s_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    return;
}

void ISDist::hard_smooth_weights()
{
    int i, clause, v;
    for (i = 0; i < large_weight_clauses_count; i++)
    {
        clause = large_weight_clauses[i];
        if (sat_count[clause] > 0)
        {
            clause_weight[clause] -= h_inc;

            if (clause_weight[clause] == 1)
            {
                large_weight_clauses[i] = large_weight_clauses[--large_weight_clauses_count];
                i--;
            }
            if (sat_count[clause] == 1)
            {
                v = sat_var[clause];
                score[v] += h_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    return;
}

void ISDist::soft_smooth_weights()
{
    int i, clause, v;

    for (i = 0; i < soft_large_weight_clauses_count; i++)
    {
        clause = soft_large_weight_clauses[i];
        if (clause_lit_count[clause] == 0)  continue;
        if (sat_count[clause] > 0)
        {
            clause_weight[clause] -= s_inc;
            if (clause_weight[clause] <= s_inc && already_in_soft_large_weight_stack[clause] == 1)
            {
                already_in_soft_large_weight_stack[clause] = 0;
                soft_large_weight_clauses[i] = soft_large_weight_clauses[--soft_large_weight_clauses_count];
                i--;
            }
            if (sat_count[clause] == 1)
            {
                v = sat_var[clause];
                score[v] += s_inc;
                if (score[v] > 0 && already_in_goodvar_stack[v] == -1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v, goodvar_stack);
                }
            }
        }
    }
    return;
}

void ISDist::update_clause_weights()
{
    if (num_hclauses > 0)
    {
        // update hard clause weight
        if (1 == local_soln_feasible && ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability && large_weight_clauses_count > large_clause_count_threshold)
        {
            hard_smooth_weights();
        }
        else
        {
            hard_increase_weights();
        }

        // update soft clause weight
        // if (1 == local_soln_feasible && ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < soft_smooth_probability && soft_large_weight_clauses_count > soft_large_clause_count_threshold)
        if (soft_unsat_weight >= opt_unsat_weight)
        {
            if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < soft_smooth_probability && soft_large_weight_clauses_count > soft_large_clause_count_threshold)
            {
                soft_smooth_weights();
            }
            else if (0 == hard_unsat_nb)
            {
                soft_increase_weights();
            }
        }
    }
    else
    {
        if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < soft_smooth_probability && soft_large_weight_clauses_count > soft_large_clause_count_threshold)
        {
            soft_smooth_weights();
        }
        else
        {
            soft_increase_weights();
        }
    }
}

void ISDist::update_clause_scores(long long s)
{
    int i, j;
    
    long long opt = soft_unsat_weight < opt_unsat_weight ? soft_unsat_weight : opt_unsat_weight;
    long long larger = pre_unsat_weight > soft_unsat_weight ? pre_unsat_weight : soft_unsat_weight;
    double stemp = ((double) s) / (larger - opt + 1);
    double discount;
    if (local_times < backward_step)
    {
        for (i = 0; i < local_times; i++)
        {
            discount = pow(gamma1, local_times - 1 - i);
            clause_score[selected_clauses[i]] += (discount * ((double) stemp));
        }
    }
    else
    {
        for (i = 0; i < backward_step; i++)
        {
            if (i == local_times % backward_step)
                continue;
            if (i < local_times % backward_step)
                discount = pow(gamma1, local_times % backward_step - 1 - i);
            else
                discount = pow(gamma1, local_times % backward_step + backward_step - 1 - i);
            clause_score[selected_clauses[i]] += (discount * ((double) stemp));
        }
    }
}

void ISDist::update_lit_scores(long long s)
{
    int i, j;
    
    long long larger = pre_unsat_hard_nb > hard_unsat_nb ? pre_unsat_hard_nb : hard_unsat_nb;
    double stemp = ((double) s) / (larger + 1);
    double discount;
    if (local_times_hard < backward_step_hard)
    {
        for (i = 0; i < local_times_hard; i++)
        {
            discount = pow(gamma1_hard, local_times_hard - 1- i);
            lit_score[selected_lits[i]] += (discount * ((double) stemp));
        }
    }
    else
    {
        for (i = 0; i < backward_step_hard; i++)
        {
            if (i == local_times_hard % backward_step_hard)
                continue;
            if (i < local_times_hard % backward_step_hard)
                discount = pow(gamma1_hard, local_times_hard % backward_step_hard - 1 - i);
            else
                discount = pow(gamma1_hard, local_times_hard % backward_step_hard + backward_step_hard - 1 - i);
            lit_score[selected_lits[i]] += (discount * ((double) stemp));
        }
    }
}
#endif
