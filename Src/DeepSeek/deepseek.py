# Please install OpenAI SDK first: `pip3 install openai`

from langchain_deepseek import ChatDeepSeek

llm = ChatDeepSeek(
    model="deepseek-chat",
    temperature=0.8,
    # max_tokens=None,
    # timeout=None,
    # max_retries=2,
    api_key="sk-17d6857565814736b9e0d60a70d684d9"
)

messages = [
    (
        "system",
        "You are a helpful assistant that translates English to French. Translate the user sentence.",
    ),
    ("human", "I love programming."),
]

print(llm.invoke(messages).content)

from openai import OpenAI

client = OpenAI(api_key="sk-17d6857565814736b9e0d60a70d684d9", base_url="https://api.deepseek.com")

response = client.chat.completions.create(
    model="deepseek-chat",
    messages=[
        {"role": "system", "content": "You are a helpful assistant"},
        {"role": "user", "content": "Hello"},
    ],
    stream=False
)

print(response.choices[0].message.content)