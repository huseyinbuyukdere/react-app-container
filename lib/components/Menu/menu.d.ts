/// <reference types="react" />
import { MenuItem as MenuItemContract } from '../../models';
interface MenuProps {
    itemList: MenuItemContract[];
    selectedRouteKey: string;
    isFlat?: boolean;
}
export default function Menu(props: MenuProps): JSX.Element;
export {};
