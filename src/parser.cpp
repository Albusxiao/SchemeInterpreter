/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 * 
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }
    //TODO: check if the first element is a symbol
    //If not, use Apply function to package to a closure;
    //If so, find whether it's a variable or a keyword;
    SymbolSyntax *id = dynamic_cast<SymbolSyntax *>(stxs[0].get());
    if (id == nullptr) {
        //TODO: TO COMPLETE THE LOGIC
        vector<Expr> listed;
        listed.clear();
        Expr ex = stxs[0]->parse(env);
        if (stxs.size()==1) {
            return Expr(new Apply(ex,listed));
        }
        if (stxs.size() >= 2) {
            for (int i = 1; i < stxs.size(); i++)listed.push_back(stxs[i]->parse(env));
            return Expr(new Apply(ex, listed));
        }
        throw(RuntimeError("Unable to parse"));
    } else {
        string op = id->s;
        if (find(op, env).get() != nullptr) {
            Value found = find(op, env);
            if (found.get() != nullptr) {
                vector<Expr> parameters;
                for (int i = 1; i < stxs.size(); ++i) {
                    parameters.push_back(stxs[i]->parse(env));
                }
                Expr e = stxs[0]->parse(env);
                return Expr(new Apply(e, parameters));
            }
            //TODO: TO COMPLETE THE PARAMETER PARSER LOGIC
        }
        if (primitives.count(op) != 0) {
            vector<Expr> parameters;
            //TODO: TO COMPLETE THE PARAMETER PARSER LOGIC
            parameters.clear();
            for (int i = 1; i < stxs.size(); i++)parameters.push_back(stxs[i]->parse(env));
            ExprType op_type = primitives[op];
            if (op_type == E_PLUS) {
                if (parameters.size() == 0)return Expr(new Plus(new Fixnum(0), new Fixnum(0)));
                if (parameters.size() == 1)return Expr(new Plus(new Fixnum(0), parameters[0]));
                if (parameters.size() == 2) {
                    return Expr(new Plus(parameters[0], parameters[1]));
                } else {
                    if (parameters.size() > 2)return Expr(new PlusVar(parameters));
                    throw RuntimeError("RuntimeError");
                }
            } else if (op_type == E_MINUS) {
                //TODO: TO COMPLETE THE LOGI
                if (parameters.size() == 1) {
                    return Expr(new Mult(new Fixnum(-1), parameters[0]));
                }
                if (parameters.size() == 2) {
                    return Expr(new Minus(parameters[0], parameters[1]));
                } else {
                    if (parameters.size() > 2)return Expr(new MinusVar(parameters));
                    throw RuntimeError("RuntimeError");
                }
            } else if (op_type == E_MUL) {
                //TODO: TO COMPLETE THE LOGIC
                if (parameters.size() == 0)return Expr(new Mult(new Fixnum(1), new Fixnum(1)));
                if (parameters.size() == 1)return Expr(new Mult(new Fixnum(1), parameters[0]));
                if (parameters.size() == 2) {
                    return Expr(new Mult(parameters[0], parameters[1]));
                } else {
                    if (parameters.size() > 2)return Expr(new MultVar(parameters));
                    throw RuntimeError("RuntimeError");
                }
            } else if (op_type == E_DIV) {
                if (parameters.size() == 1)return Expr(new Div(new Fixnum(1), parameters[0]));
                if (parameters.size() == 2) {
                    return Expr(new Div(parameters[0], parameters[1]));
                } else {
                    if (parameters.size() > 2)return Expr(new DivVar(parameters));
                    throw RuntimeError("RuntimeError");
                }
            } else if (op_type == E_MODULO) {
                if (parameters.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for modulo");
                }
                return Expr(new Modulo(parameters[0], parameters[1]));
            } else if (op_type == E_LIST) {
                return Expr(new ListFunc(parameters));
            } else if (op_type == E_LT) {
                if (parameters.size() == 2)return Expr(new Less(parameters[0], parameters[1]));
                else if (parameters.size() > 2)return Expr(new LessVar(parameters));
            } else if (op_type == E_LE) {
                if (parameters.size() == 2)return Expr(new LessEq(parameters[0], parameters[1]));
                else if (parameters.size() > 2)return Expr(new LessEqVar(parameters));
            } else if (op_type == E_EQ) {
                if (parameters.size() == 2)return Expr(new Equal(parameters[0], parameters[1]));
                else if (parameters.size() > 2)return Expr(new EqualVar(parameters));
            } else if (op_type == E_GE) {
                if (parameters.size() == 2)return Expr(new GreaterEq(parameters[0], parameters[1]));
                else if (parameters.size() > 2)return Expr(new GreaterEqVar(parameters));
            } else if (op_type == E_GT) {
                if (parameters.size() == 2)return Expr(new Greater(parameters[0], parameters[1]));
                else if (parameters.size() > 2)return Expr(new GreaterVar(parameters));
            } else if (op_type == E_AND) {
                return Expr(new AndVar(parameters));
            } else if (op_type == E_OR) {
                return Expr(new OrVar(parameters));
            } else if (op_type == E_NOT) {
                if (parameters.size() == 1)return Expr(new Not(parameters[0]));
                else throw(RuntimeError("Wrong expr numbers in Not"));
            } else if (op_type == E_CONS) {
                if (parameters.size() == 2)return Expr(new Cons(parameters[0], parameters[1]));
                throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_CAR) {
                if (parameters.size() == 1)return Expr(new Car(parameters[0]));
                throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_CDR) {
                if (parameters.size() == 1)return Expr(new Cdr(parameters[0]));
                throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_LIST) {
                return Expr(new ListFunc(parameters));
            } else if (op_type == E_LISTQ) {
                if (parameters.size() == 1)return Expr(new IsList(parameters[0]));
                throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_SETCAR) {
                if (parameters.size() == 2)return Expr(new SetCar(parameters[0], parameters[1]));
                throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_SETCDR) {
                if (parameters.size() == 2)return Expr(new SetCdr(parameters[0], parameters[1]));
                throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_VOID) {
                if (!parameters.empty())throw(RuntimeError("No parameters for void"));
                return Expr(new MakeVoid());
            } else if (op_type == E_EXIT) {
                if (parameters.size() > 0)throw(RuntimeError("Wrong parameter number"));
                return Expr(new Exit());
            } else if (op_type == E_EQQ) {
                if (parameters.size() == 2)return Expr(new IsEq(parameters[0], parameters[1]));
                else throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_BOOLQ) {
                if (parameters.size() == 1)return Expr(new IsBoolean(parameters[0]));
                else throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_INTQ) {
                if (parameters.size() == 1)return Expr(new IsFixnum(parameters[0]));
                else throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_NULLQ) {
                if (parameters.size() == 1)return Expr(new IsNull(parameters[0]));
                else throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_PAIRQ) {
                if (parameters.size() == 1)return Expr(new IsPair(parameters[0]));
                else throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_PROCQ) {
                if (parameters.size() == 1)return Expr(new IsProcedure(parameters[0]));
                else throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_SYMBOLQ) {
                if (parameters.size() == 1)return Expr(new IsSymbol(parameters[0]));
                else throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_STRINGQ) {
                if (parameters.size() == 1)return Expr(new IsString(parameters[0]));
                else throw(RuntimeError("Wrong parameter number"));
            } else if (op_type == E_DISPLAY) {
                if (parameters.size()==1)return Expr(new Display(parameters[0]));
                else throw(RuntimeError("Wrong parameter number"));
            }
        }
        if (reserved_words.count(op) != 0) {
            switch (reserved_words[op]) {
                case E_QUOTE: {
                    if (stxs.size() == 2)return Expr(new Quote(stxs[1]));
                    else throw(RuntimeError("Wrong expr numbers in Quote"));
                }
                case E_BEGIN: {
                    vector<Expr> temp;
                    temp.clear();
                    for (int i = 1; i < stxs.size(); i++)temp.emplace_back(stxs[i]->parse(env));
                    return Expr(new Begin(temp));
                }
                case E_IF: {
                    if (stxs.size() == 4)
                        return Expr(new If(stxs[1]->parse(env), stxs[2]->parse(env),
                                           stxs[3]->parse(env)));
                    throw ("Wrong in IF");
                }
                case E_COND: {
                    vector<vector<Expr> > temp;
                    temp.clear();
                    for (int i = 1; i < stxs.size(); i++) {
                        if (dynamic_cast<List *>(stxs[i].get())) {
                            vector<Expr> tep;
                            tep.clear();
                            List *temp_ls = dynamic_cast<List *>(stxs[i].get());
                            if (dynamic_cast<SymbolSyntax *>(temp_ls->stxs[0].get()) && dynamic_cast<SymbolSyntax *>(
                                    temp_ls->stxs[0].get())->s == "else")
                                tep.push_back(Expr(new True));
                            else tep.push_back(temp_ls->stxs[0]->parse(env));
                            for (int j = 1; j < temp_ls->stxs.size(); j++)tep.push_back(temp_ls->stxs[j]->parse(env));
                            temp.push_back(tep);
                        } else throw (RuntimeError("Wrong in Cond"));
                    }
                    return Expr(new Cond(temp));
                }
                case E_LAMBDA: {
                    if (stxs.size() >= 3) {
                        if (dynamic_cast<List *>(stxs[1].get())) {
                            List *temp_ls = dynamic_cast<List *>(stxs[1].get());
                            vector<string> parameters;
                            parameters.clear();
                            Assoc temp_as = env;
                            for (int i = 0; i < temp_ls->stxs.size(); i++) {
                                if (dynamic_cast<SymbolSyntax *>(temp_ls->stxs[i].get())) {
                                    parameters.push_back(dynamic_cast<SymbolSyntax *>(temp_ls->stxs[i].get())->s);
                                    temp_as = extend(parameters.back(), VoidV(), temp_as);
                                } else throw(RuntimeError("Wrong in Lambda"));
                            }
                            Expr e = nullptr;
                            vector<Expr> temp;
                            temp.clear();
                            if (stxs.size() == 3)e = stxs[2]->parse(temp_as);
                            else {
                                for (int i = 2; i < stxs.size(); i++)temp.push_back(stxs[i]->parse(temp_as));
                                e = Expr(new Begin(temp));
                            }
                            return Expr(new Lambda(parameters, e));
                        } else throw(RuntimeError("Wrong format in Lambada"));
                    } else throw(RuntimeError("Wrong format in Lambada"));
                }
                case E_DEFINE: {
                    if (stxs.size() < 3) throw(RuntimeError("Wrong format in Define"));
                    if (dynamic_cast<SymbolSyntax *>(stxs[1].get())) {
                        string name = dynamic_cast<SymbolSyntax *>(stxs[1].get())->s;
                        env = extend(name, VoidV(), env);
                        Expr ex=stxs[2]->parse(env);
                        if (stxs.size() == 3)return Expr(new Define(name, ex));
                        else throw(RuntimeError("Couldn't bind several procedures to a VAR identifier"));
                    }
                    if (dynamic_cast<List *>(stxs[1].get())) {
                        List *stx1_ls = dynamic_cast<List *>(stxs[1].get());
                        string name;
                        if (dynamic_cast<SymbolSyntax *>(stx1_ls->stxs[0].get()))
                            name = dynamic_cast<SymbolSyntax *>(stx1_ls->stxs[0].get())->s;
                        else throw(RuntimeError("Wrong in Define a Procedure"));
                        vector<string> parameters;
                        parameters.clear();
                        env = extend(name, VoidV(), env);
                        for (int i = 1; i < stx1_ls->stxs.size(); i++) {
                            if (dynamic_cast<SymbolSyntax *>(stx1_ls->stxs[i].get())) {
                                parameters.push_back(dynamic_cast<SymbolSyntax *>(stx1_ls->stxs[i].get())->s);
                                env = extend(parameters.back(), VoidV(), env);
                            } else throw(RuntimeError("Wrong in Define a Procedure"));
                        }
                        if (stxs.size() == 3)return Expr(new Define(name, new Lambda(parameters,stxs[2]->parse(env))));
                        else {
                            vector<Expr> temp_ls;
                            temp_ls.clear();
                            for (int i = 2; i < stxs.size(); i++)temp_ls.emplace_back(stxs[i]->parse(env));
                            return Expr(new Define(name, new Lambda(parameters,new Begin(temp_ls))));
                        }
                    }
                }
                case E_LET: {
                    if (stxs.size() < 3) throw(RuntimeError("Wrong format in Let"));
                    if (dynamic_cast<List *>(stxs[1].get())) {
                        List *temp_ls = dynamic_cast<List *>(stxs[1].get());
                        vector<pair<string, Expr> > parameters;
                        parameters.clear();
                        Assoc temp_env = env;
                        for (int i = 0; i < temp_ls->stxs.size(); i++) {
                            List *temp_lst = dynamic_cast<List *>(temp_ls->stxs[i].get());
                            if (temp_lst != nullptr && temp_lst->stxs.size() == 2) {
                                if (dynamic_cast<SymbolSyntax *>(temp_lst->stxs[0].get())) {
                                    parameters.push_back({
                                        dynamic_cast<SymbolSyntax *>(temp_lst->stxs[0].get())->s,
                                        temp_lst->stxs[1]->parse(env)
                                    });
                                    temp_env = extend(dynamic_cast<SymbolSyntax *>(temp_lst->stxs[0].get())->s, VoidV(),
                                                      temp_env);
                                } else throw(RuntimeError("Wrong in Let"));
                            } else throw(RuntimeError("Wrong in Let's parameters"));
                        }
                        Expr e = nullptr;
                        vector<Expr> temp;
                        temp.clear();
                        if (stxs.size() == 3)e = stxs[2]->parse(temp_env);
                        else {
                            for (int i = 2; i < stxs.size(); i++)temp.push_back(stxs[i]->parse(temp_env));
                            e = Expr(new Begin(temp));
                        }
                        return Expr(new Let(parameters, e));
                    } else throw (RuntimeError("Wrong in Let"));
                }
                case E_LETREC: {
                    if (stxs.size() != 3) throw(RuntimeError("Wrong format in Letrec"));
                    if (dynamic_cast<List *>(stxs[1].get())) {
                        List *temp_ls = dynamic_cast<List *>(stxs[1].get());
                        vector<pair<string, Expr> > parameters;
                        parameters.clear();

                        // First collect all names and create a temporary env with placeholders
                        Assoc temp_env = env;
                        for (int i = 0; i < temp_ls->stxs.size(); i++) {
                            List *temp_lst = dynamic_cast<List *>(temp_ls->stxs[i].get());
                            if (temp_lst != nullptr && temp_lst->stxs.size() == 2) {
                                if (dynamic_cast<SymbolSyntax *>(temp_lst->stxs[0].get())) {
                                    string name = dynamic_cast<SymbolSyntax *>(temp_lst->stxs[0].get())->s;
                                    // add placeholder so that bindings can refer to each other during parsing
                                    temp_env = extend(name, VoidV(), temp_env);
                                } else throw(RuntimeError("Wrong in Letrec"));
                            } else throw(RuntimeError("Wrong in Letrec's parameters"));
                        }
                        for (int i = 0; i < temp_ls->stxs.size(); i++) {
                            List *temp_lst = dynamic_cast<List *>(temp_ls->stxs[i].get());
                            string name = dynamic_cast<SymbolSyntax *>(temp_lst->stxs[0].get())->s;
                            Expr rhs = temp_lst->stxs[1]->parse(temp_env);
                            parameters.push_back({name, rhs});
                        }
                        Expr e = nullptr;
                        vector<Expr> temp;
                        temp.clear();
                        if (stxs.size() == 3) e = stxs[2]->parse(temp_env);
                        else {
                            for (int i = 2; i < stxs.size(); i++) temp.push_back(stxs[i]->parse(temp_env));
                            e = Expr(new Begin(temp));
                        }
                        return Expr(new Letrec(parameters, e));
                    } else throw (RuntimeError("Wrong in Letrec"));
                }
                case E_SET: {
                    if (stxs.size() != 3) throw(RuntimeError("Wrong format in Set"));
                    if (dynamic_cast<SymbolSyntax *>(stxs[1].get())) {
                        string name = dynamic_cast<SymbolSyntax *>(stxs[1].get())->s;
                        if (find(name, env).get() != nullptr)return Expr(new Set(name, stxs[2]->parse(env)));
                        else throw(RuntimeError("Undefined var"));
                    } else throw(RuntimeError("Wrong in Set"));
                }
                default:
                    throw RuntimeError("Unknown reserved word: " + op);
            }
        }
        vector<Expr> parameters;
        parameters.clear();
        for (int i = 1; i < stxs.size(); i++)parameters.push_back(stxs[i]->parse(env));
        return Expr(new Apply(new Var(dynamic_cast<SymbolSyntax *>(stxs[0].get())->s), parameters));
        //default: use Apply to be an expression
        //TODO: TO COMPLETE THE PARSER LOGIC
        throw(RuntimeError("Unable to parse: " + op));
    }
}
