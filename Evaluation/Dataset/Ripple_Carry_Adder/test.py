import json

with open("Evaluation/Dataset/Ripple_Carry_Adder/explanation.json") as jsonfile:
    data = json.load(jsonfile)
    for assertion, details in data.items():
        explanation = details.get("Assertion Explaination", "No explanation provided")
        print(f"{assertion}: {explanation}")

