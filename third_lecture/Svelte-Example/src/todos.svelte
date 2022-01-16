<script lang="ts">
    let todos = [
        {done:false, text:'1'},
        {done:false, text:'2'},
        {done:false, text:'3'},
        {done:false, text:'4'}
    ];

    function add() {
        todos = todos.concat({done:false, text:''});
    }

    function clear() {
        todos = todos.filter(t => !t.done);
    }

    function remove(index: number) {
        todos.splice(index, 1)
        todos = todos;
    }

    $: remaining = todos.filter(t => !t.done).length;
</script>

<h1> Todo-Lists </h1>

{#each todos as todo, index}
    <div>
      <input 
        type=checkbox 
        bind:checked={todo.done}
      >
      <input 
        placeholder="What needs to be done?" 
        bind:value={todo.text} 
        disabled={todo.done}
      >
      <button on:click={() => remove(index)}>delete</button>
    </div>
{/each}

<p> {remaining} remaining </p>

<button on:click={add}> 
    Add new 
</button>

<button on:click={clear}> 
    Clear completed 
</button>