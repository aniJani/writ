import { simpleGate } from "@anijani/writ/simple"

const askUser = async (question: string) => { console.log(`ask: ${question}`); return true }
const w = await simpleGate({ user: "user:alice", tools: { web_search: "none", send_email: "per_call" } })
const s = await w.session()

const search = await s.propose("web_search", { q: "tea" })
console.log("search:", await s.run(search, async () => "3 results"))

let email = await s.propose("send_email", { to: "bob@example.com", body: "Tea at four?" })
if (email.status === "needs_approval" && await askUser("Email bob@example.com?")) email = await s.approve(email)
console.log("email:", await s.run(email, async () => "sent"))
