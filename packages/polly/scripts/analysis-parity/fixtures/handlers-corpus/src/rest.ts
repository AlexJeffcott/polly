import { Elysia } from "elysia";
import { handleAdd } from "./impl";
import { counter } from "./state";

const createItem = () => {
  counter.value.count = 3;
};

new Elysia().get("/items", handleAdd).post("/items", createItem);
