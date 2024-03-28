import re

def eliminate_implication(formula):
    formula = re.sub(r'(\w+\(.*?\))\s*==>\s*(\w+\(.*?\))', r'(!\1 | \2)', formula)
    formula = re.sub(r'(\w+\(.*?\))\s*<->\s*(\w+\(.*?\))', r'(!\1 | \2) & (\1 | !\2)', formula)
    return formula

def move_negation_inward(formula):
    formula = re.sub(r'!\(\s*(\w+)\s*&\s*(\w+)\s*\)', r'(!\1 | !\2)', formula)
    formula = re.sub(r'!\(\s*(\w+)\s*\|\s*(\w+)\s*\)', r'(!\1 & !\2)', formula)
    formula = re.sub(r'!∀\s*(\w+)\s*(\w+)', r'∃\1 !\2', formula)
    formula = re.sub(r'!∃\s*(\w+)\s*(\w+)', r'∀\1 !\2', formula)
    return formula

def remove_double_not(formula):
    return re.sub(r'!!(\w+\(.*?\))', r'\1', formula)

def standardize_variable(expression):
    unique_vars = set()
    def replace_var(match):
        var = match.group(1)
        if var in unique_vars:
            for letter in "abcdefghijklmnopqrstuvwxyz":
                if letter not in unique_vars:
                    unique_vars.add(letter)
                    return letter
        else:
            unique_vars.add(var)
            return var

    expression = re.sub(r'(\w+)\((\w+)\)', r'\1(\2)', expression)

    expression = re.sub(r'(\w+)', replace_var, expression)

    return expression

def prenex_form(formula):
    parts = formula.split('|')
    quantifiers = []
    predicates = []

    for part in parts:
        quantifier = re.findall(r'(∀|∃)(\w+)', part)
        if quantifier:
            quantifiers.extend(quantifier)
            part = re.sub(r'(∀|∃)\w+\s*', '', part)
        predicates.append(part)

    quantifier_str = ' '.join([f"{q[0]}{q[1]}" for q in quantifiers])

    if quantifier_str:
        return f"{quantifier_str} {'|'.join(predicates)}"
    else:
        return '|'.join(predicates)

def skolemization(formula):
    return re.sub(r'∃(\w+)\s*(\w+)', r'\2', formula)

def drop_universal(formula):
    return re.sub(r'∀(\w+)\s*(\w+)', r'\2', formula)

def convert_to_cnf(formula):
    pattern = r'(\w+)\s*\|\s*\((\w+)\s*&\s*(\w+)\)'

    def distribute(match):
        p, q, r = match.groups()
        return f'({p} | {q}) & ({p} | {r})'

    return re.sub(pattern, distribute, formula)

def turn_conjunction(cnf_formula):
    clauses = cnf_formula.split('|')
    renamed_clauses = []
    variables_count = {}

    for idx, clause in enumerate(clauses, start=1):
        def repl(match):
            var = match.group(0)
            count = variables_count.get(var, 0) + 1
            variables_count[var] = count
            return var + str(count)

        clause = re.sub(r'\b(\w+)\b', repl, clause)
        renamed_clauses.append('C{}: {}'.format(idx, clause))

    return '{' + ', '.join(renamed_clauses) + '}'

def rename_variables(formula):
    variables_count = {}
    def repl(match):
        var = match.group(0)
        count = variables_count.get(var, 0) + 1
        variables_count[var] = count
        return var + str(count)

    formula = re.sub(r'\b(\w+)\b', repl, formula)
    return formula

def remove_brackets(statement):
    updated_statement = re.sub(r'\((\b\w+\b|\w+)\)', '', statement)
    return updated_statement

def modify__statements(formula):
        formula = eliminate_implication(formula)
        formula = move_negation_inward(formula)
        formula = remove_double_not(formula)
        formula = standardize_variable(formula)
        formula = prenex_form(formula)
        formula = skolemization(formula)
        formula = drop_universal(formula)
        formula = convert_to_cnf(formula)
        formula = remove_brackets(formula) 
        return formula

def resolution(resolutions):
    # Iterate from the end of the list to avoid index errors
    for i in range(len(resolutions) - 1, -1, -1):
        clause = resolutions[i]
        for j in range(i - 1, -1, -1):
            # Check if there's a complementary literal in the list
            if len(clause) == len(resolutions[j]) and \
               sum(a != b for a, b in zip(clause, resolutions[j])) == 1:
                # Remove the complementary literals
                resolutions.pop(j)
                resolutions.pop(i)
                break

    # Remove anything that isn't a letter
    resolutions = [clause for clause in resolutions if clause.isalpha()]

    return resolutions if len(resolutions) > 1 else []

case1 = "P(x) ==> Q(x)"
case2 = "!Q(x) | r(x)"
case3 = "W(x) ==> T(x)"
case4 = "!R(x) | W(x)"
case5 = "P(x)"
case6 = "!T(x)"

case1 = modify__statements(case1)
case2 = modify__statements(case2)
case3 = modify__statements(case3)
case4 = modify__statements(case4)
case5 = modify__statements(case5)
case6 = modify__statements(case6)

list_resolution = [case1, case2, case3, case4, case5, case6]
print("The list before resultion: ", list_resolution)

list_resolution = resolution(list_resolution)
print("The list after resultion: ", list_resolution)


# formula = "P(x) ==> Q(x)"
# result = eliminate_implication(formula)
# print("Original form:", formula)
# print("Final result:", result)
# print("")

# formula = "(P(x) <-> Q(x))"
# result = eliminate_implication(formula)
# print("Original form:", formula)
# print("Final result:", result)
# print("")

# formula = "!(p & q)"
# result = move_negation_inward(formula)
# print("Original form:", formula)
# print("Final result:", result)
# print("")

# formula = "!!P(x)"
# result = remove_double_not(formula)
# print("Original form:", formula)
# print("Final result:", result)
# print("")

# formula = "P(x) | Q(x)"
# result = standardize_variable(formula)
# print("Original form:", formula)
# print("Final result:", result)
# print("")

# formula = "(∀x P(x)) & (∃y Q(x))"
# result = prenex_form(formula)
# print("Original form:", formula)
# print("Final result:", result)
# print("")

# formula = "(∃xP(x))  & (∃y Q(x))"
# result = skolemization(formula)
# print("Original form:", formula)
# print("Final result:", result)
# print("")

# formula = "(∀xP(x))  & (∀y Q(x))"
# result = drop_universal(formula)
# print("Original form:", formula)
# print("Final result:", result)
# print("")

# formula = "p | (q & r)"
# result = convert_to_cnf(formula)
# print("Original form:", formula)
# print("Final result:", result)
# print("")

# formula = "(P(x) & Q(y)) | (R(z) & S(w))"
# result = turn_conjunction(formula)
# print("Original form:", formula)
# print("Final result:", result)
# print("")

# formula = "(P(x) & Q(y)) | (R(z) & S(w))"
# result = rename_variables(formula)
# print("Original form:", formula)
# print("Final result:", result)
# print("")

# Kb = "!(P(x) | Q(x))"
# list_done = ['']
# alpha = "P(x)"
# # kb_dash = Kb.split(" ")
# print(Kb)


# result = eliminate_implication(Kb)
# result = move_negation_inward(result)
# result = remove_double_not(result)
# result = standardize_variable(result)
# result = prenex_form(result)
# result = skolemization(result)
# result = drop_universal(result)
# result = convert_to_cnf(result)
# # result = turn_conjunction(result)
# # result = rename_variables(result)
# print(result)

# print(Kb)
