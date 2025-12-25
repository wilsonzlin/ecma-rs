const promise: Promise<string> = Promise.resolve("ok");

document.addEventListener("click", (event) => {
  console.log(event.type);
});
