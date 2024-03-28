import re

def eliminate_implication(formula):
    formula = re.sub(r'(\w+\(.*?\))\s*==>\s*(\w+\(.*?\))', r'(!\1 | \2)', formula)
    formula = re.sub(r'(\w+\(.*?\))\s*<->\s*(\w+\(.*?\))', r'(!\1 | \2) & (!\2 | \1)', formula)
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
    # Replace duplicate variables with unique names (a-z)
    unique_vars = set()
    def replace_var(match):
        var = match.group(1)
        if var in unique_vars:
            # Find the next available letter (a-z)
            for letter in "abcdefghijklmnopqrstuvwxyz":
                if letter not in unique_vars:
                    unique_vars.add(letter)
                    return letter
        else:
            unique_vars.add(var)
            return var

    # Replace variables inside function brackets
    expression = re.sub(r'(\w+)\((\w+)\)', r'\1(\2)', expression)

    # Replace duplicate variables
    expression = re.sub(r'(\w+)', replace_var, expression)

    return expression

def prenex_form(formula):
    # Extract quantifiers and predicates from the formula
    parts = formula.split('|')
    quantifiers = []
    predicates = []

    for part in parts:
        # Match quantifiers and the character following them
        quantifier = re.findall(r'(∀|∃)(\w+)', part)
        if quantifier:
            quantifiers.extend(quantifier)
            # Remove quantifiers and their associated variables
            part = re.sub(r'(∀|∃)\w+\s*', '', part)
        predicates.append(part)

    # Construct quantifier string with associated variables
    quantifier_str = ' '.join([f"{q[0]}{q[1]}" for q in quantifiers])

    # Add quantifier string to the beginning of the statements
    if quantifier_str:
        return f"{quantifier_str} {'|'.join(predicates)}"
    else:
        return '|'.join(predicates)

def skolemization(formula):
    variables = re.findall(r'∃\w+\s*(\w+)', formula)
    for var in variables:
        formula = re.sub(r'∃\w+\s*' + var, var, formula)
    formula = re.sub(r'∀\w+\s*(\w+)\s*∃(\w+)\s*(\w+)', r'\1 | \3', formula)
    formula = re.sub(r'∀(\w+)\s*∃(\w+)\s*(\w+)', r'∀\1 \3', formula)
    return formula

def drop_universal(formula):
    return re.sub(r'∀(\w+)\s*(\w+)', r'\2', formula)

def convert_to_cnf(formula):
    pattern = r'(\w+)\s*\|\s*\((\w+)\s*&\s*(\w+)\)'

    def distribute(match):
        p, q, r = match.groups()
        return f'({p} | {q}) & ({p} | {r})'

    return re.sub(pattern, distribute, formula)

def turn_conjunction(cnf_formula):
    clauses = cnf_formula.split('&')
    renamed_clauses = []
    variables_count = {}

    for idx, clause in enumerate(clauses, start=1):
        # Rename variables within the clause
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


formula = "(P(x) ==> Q(x))"
result = eliminate_implication(formula)
print("Original form:", formula)
print("Final result:", result)
print("")

formula = "(P(x) <-> Q(x))"
result = eliminate_implication(formula)
print("Original form:", formula)
print("Final result:", result)
print("")

formula = "!(p & q)"
result = move_negation_inward(formula)
print("Original form:", formula)
print("Final result:", result)
print("")


formula = "!!(P(x) | Q(x))"
result = remove_double_not(formula)
print("Original form:", formula)
print("Final result:", result)
print("")

formula = "P(x) | Q(x)"
result = standardize_variable(formula)
print("Original form:", formula)
print("Final result:", result)
print("")

formula = "(∀x P(x)) & (∃y Q(x))"
result = prenex_form(formula)
print("Original form:", formula)
print("Final result:", result)
print("")

formula = "(∃xP(x))  & (∃y Q(x))"
result = skolemization(formula)
print("Original form:", formula)
print("Final result:", result)
print("")

formula = "(∀xP(x))  & (∀y Q(x))"
result = drop_universal(formula)
print("Original form:", formula)
print("Final result:", result)
print("")

formula = "p | (q & r)"
result = convert_to_cnf(formula)
print("Original form:", formula)
print("Final result:", result)
print("")

formula = "(P(x) & Q(y)) | (R(z) & S(w))"
result = turn_conjunction(formula)
print("Original form:", formula)
print("Final result:", result)
print("")

formula = "(P(x) & Q(y)) | (R(z) & S(w))"
result = rename_variables(formula)
print("Original form:", formula)
print("Final result:", result)
print("")
