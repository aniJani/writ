"""The quick start in README.md: one free call and one call the user approves."""

from writ import simple_gate


def ask_user(question: str) -> bool:
    print(f"ask: {question}")
    return True


w = simple_gate({"web_search": "none", "send_email": "per_call"}, user="user:alice")
s = w.session()

search = s.propose("web_search", {"q": "tea"})
print("search:", s.run(search, lambda: "3 results"))

email = s.propose("send_email", {"to": "bob@example.com", "body": "Tea at four?"})
if email.status == "needs_approval" and ask_user("Email bob@example.com?"):
    email = s.approve(email)
print("email:", s.run(email, lambda: "sent"))
