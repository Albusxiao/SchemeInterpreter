#include "Def.hpp"
#include "syntax.hpp"
#include "expr.hpp"
#include "value.hpp"
#include "RE.hpp"
#include <sstream>
#include <iostream>
#include <map>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;
/*
bool isExplicitVoidCall(Expr expr) {
    MakeVoid* make_void_expr = dynamic_cast<MakeVoid*>(expr.get());
    if (make_void_expr != nullptr) {
        return true;
    }
    
    Apply* apply_expr = dynamic_cast<Apply*>(expr.get());
    if (apply_expr != nullptr) {
        Var* var_expr = dynamic_cast<Var*>(apply_expr->rator.get());
        if (var_expr != nullptr && var_expr->x == "void") {
            return true;
        }
    }
    
    Begin* begin_expr = dynamic_cast<Begin*>(expr.get());
    if (begin_expr != nullptr && !begin_expr->es.empty()) {
        return isExplicitVoidCall(begin_expr->es.back());
    }
    
    If* if_expr = dynamic_cast<If*>(expr.get());
    if (if_expr != nullptr) {
        return isExplicitVoidCall(if_expr->conseq) || isExplicitVoidCall(if_expr->alter);
    }
    
    Cond* cond_expr = dynamic_cast<Cond*>(expr.get());
    if (cond_expr != nullptr) {
        for (const auto& clause : cond_expr->clauses) {
            if (clause.size() > 1 && isExplicitVoidCall(clause.back())) {
                return true;
            }
        }
    }
    return false;
}*/
void REPL(){
    // read - evaluation - print loop
    Assoc global_env = empty();
    bool flag = true;
     std::vector<std::pair<std::string, Expr>> defines;
    while (1){
        #ifndef ONLINE_JUDGE
        if(flag)std::cout<<"scm> ";
        #endif
        Syntax stx = readSyntax(std :: cin); // read
        try{
            Expr expr = stx -> parse(global_env);
            Define* define_expr = dynamic_cast<Define*>(expr.get());
            if (define_expr != nullptr) {
                defines.push_back({define_expr->var, define_expr->e});
                flag = false;
                continue;
            } else if (!defines.empty()) {
                for (const auto& def : defines) global_env = extend(def.first, NullV(), global_env);
                for (const auto& def : defines) {
                    Value value = def.second->eval(global_env);
                    modify(def.first, value, global_env);
                }
                defines.clear();
                Value val = expr -> eval(global_env);
                if (val -> v_type == V_TERMINATE)break;
                if (expr->e_type==E_DISPLAY) {
                    flag=true;
                    puts("");
                    continue;
                }
                if(expr->e_type==E_VOID||val->v_type!=V_VOID||
                   expr->e_type==E_BEGIN||expr->e_type==E_IF||
                   expr->e_type==E_COND||expr->e_type==E_APPLY) {
                    val -> show(std :: cout);
                    flag=true;
                   } else flag=false;
            } else {
                Value val = expr -> eval(global_env);
                if (val -> v_type == V_TERMINATE)break;
                if (expr->e_type==E_DISPLAY) {
                    flag=true;
                    puts("");
                    continue;
                }
                if(expr->e_type==E_VOID||val->v_type!=V_VOID||
                   expr->e_type==E_BEGIN||expr->e_type==E_IF||
                   expr->e_type==E_COND||expr->e_type==E_APPLY) {
                    val -> show(std :: cout);
                    flag=true;
                   } else flag=false;
            }
        }
        catch (const RuntimeError &RE){
             // std :: cout << RE.message();
            std :: cout << "RuntimeError";
            flag=true;
        }
        if (flag)puts("");
    }
}


int main(int argc, char *argv[]) {
    REPL();
    return 0;
}
