<script lang="ts">
    import { writable, derived } from 'svelte/store';

    const el = writable();
    const height = derived(el, ($el: Element, set: (arg0: number) => void) => {
        if (!$el) return;
        const ro = new ResizeObserver(([entry]) => {
            set(entry.contentRect.height);
        });
        ro.observe($el);
        return () => ro.disconnect();
    });
</script>

<textarea bind:this={$el}></textarea>

<p>
    height: {$height}px
</p>