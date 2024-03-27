def elimination_implication(statements):
    new_statements = []
    for statement in statements:
        if '-->' in statement:
            p, q = statement.split('-->')
            new_statements.append('!' + p + '|' + q)
        elif '<->' in statement:
            p, q = statement.split('<->')
            new_statements.append('(!' + p + '|' + q + ')&(!' + q + '|' + p + ')')
        else:
            new_statements.append(statement)
    return new_statements

def move_negation_inward(statements):
    new_statements = []
    for statement in statements:
        if "!!" in statement:
            new_statements.append(statement.replace("!!", ""))
        else:
            new_statements.append(statement)
    return new_statements

import re

def eliminate_implication(formula):
    formula = re.sub(r'(\w+\(.*?\))\s*==>\s*(\w+\(.*?\))', r'(!\1 | \2)', formula)
    formula = re.sub(r'(\w+\(.*?\))\s*<->\s*(\w+\(.*?\))', r'(!\1 | \2) & (!\2 | \1)', formula)
    return formula

def move_negation_inward(formula):
    while '!!' in formula:
        formula = formula.replace('!!', '')
    formula = re.sub(r'!(\w+\(.*?\))\s*&\s*!(\w+\(.*?\))', r'!\1 | \2', formula)
    formula = re.sub(r'!(\w+\(.*?\))\s*\|\s*!(\w+\(.*?\))', r'!\1 & \2', formula)
    formula = re.sub(r'!∀\s*(\w+)\s*(\w+)', r'∃\1 !\2', formula)
    formula = re.sub(r'!∃\s*(\w+)\s*(\w+)', r'∀\1 !\2', formula)
    return formula

def remove_double_not(formula):
    return re.sub(r'!!(\w+\(.*?\))', r'\1', formula)

def standardize_variable_scope(formula):
    return re.sub(r'(∀\w+\s+\w+)\s*\|\s*(∃\w+\s+\w+)', r'\1 | \2', formula)

def prenex_form(formula):
    parts = formula.split(' | ')
    quantifiers = [part for part in parts if '∀' in part or '∃' in part]
    predicates = [part for part in parts if part not in quantifiers]
    return ' | '.join(quantifiers + predicates)

def skolemization(formula):
    variables = re.findall(r'∃\w+\s*(\w+)', formula)
    for var in variables:
        formula = re.sub(r'∃\w+\s*' + var, var, formula)
    formula = re.sub(r'∀\w+\s*(\w+)\s*∃(\w+)\s*(\w+)', r'\1 | \3', formula)
    formula = re.sub(r'∀(\w+)\s*∃(\w+)\s*(\w+)', r'∀\1 \3', formula)
    return formula

def eliminate_universal_quantifiers(formula):
    return re.sub(r'∀(\w+)\s*(\w+)', r'\2', formula)

def convert_to_cnf(formula):
    formula = formula.replace('(', '').replace(')', '')
    parts = formula.split('&')
    clauses = []
    for part in parts:
        if '|' in part:
            clauses.append('(' + part + ')')
        else:
            clauses.extend(part.split('|'))
    return ' & '.join(clauses)

def rename_variables(clauses):
    unique_variables = set()
    for i, clause in enumerate(clauses):
        variables = re.findall(r'\w+\(.*?\)', clause)
        for var in variables:
            if var not in unique_variables:
                unique_variables.add(var)
                new_var = 'x' + str(len(unique_variables))
                clauses[i] = clauses[i].replace(var, new_var)
    return clauses

def resolution_procedure(formula):
    # Step 1: Eliminate Implication
    formula = eliminate_implication(formula)
    # Step 2: Move Negation Inward
    formula = move_negation_inward(formula)
    # Step 3: Remove Double Not
    formula = remove_double_not(formula)
    # Step 4: Standardize Variable Scope
    formula = standardize_variable_scope(formula)
    # Step 5: Prenex Form
    formula = prenex_form(formula)
    # Step 6: Skolemization
    formula = skolemization(formula)
    # Step 7: Eliminate Universal Quantifiers
    formula = eliminate_universal_quantifiers(formula)
    # Step 8: Convert to Conjunctive Normal Form
    formula = convert_to_cnf(formula)
    # Step 9: Turn conjunctions into clauses in a set
    clauses = formula.split('&')
    # Step 10: Rename variables in clauses
    clauses = rename_variables(clauses)
    formula = ' & '.join(clauses)
    
    return formula

# Example usage
formula = "!!p"
result = remove_double_not(formula)
print("Final result:", result)